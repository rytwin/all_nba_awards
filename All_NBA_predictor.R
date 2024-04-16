library(tidyverse)
library(rvest)
library(XML)
library(caret)
library(plotly)
library(formattable)
library(ggalt)
library(ggtext)
library(scales)
library(stringr)


############################# FUNCTIONS ###############################


# function that takes a url and table number from that url, and returns the table
# as a dataframe.
# specifically for use with basketball reference because it removes the comments
# in the html code that causes the tables on the website to not be recognized as
# tables

scrape_bballref <- function(url, table_id) {
    ## read in data from the webpage
    urltxt <- readLines(url)
    ## REMOVE COMMENT TAGS
    urltxt <- gsub("-->", "", gsub("<!--", "", urltxt))
    ## PARSE UNCOMMENTED TEXT
    doc <- htmlParse(urltxt)
    ## RETRIEVE ALL <table> TAGS
    tables <- xpathApply(doc, "//table")
    ## LIST OF DATAFRAMES
    teamPageTables <- tryCatch(lapply(tables[table_id], function(i) readHTMLTable(i)), 
                               error = function(cond) {
                                   message("ERROR (but continued running): ", url)
                                   return(NULL)
                               })
    return(teamPageTables)
}


# function that takes a vector of years and scrapes basketball reference's draft
# pages, and returns every pick in the draft from those years in a dataframe

scrape_draft <- function(years) {
    
    tbls_all <- data.frame()
    
    for (y in years) {
        webpage <- read_html(paste0("https://www.basketball-reference.com/draft/NBA_",
                                    y, ".html"))
        tbls <- webpage %>% 
            html_nodes("#stats") %>%
            html_table(fill = TRUE)
        colnames(tbls[[1]]) <- c("X", "Pick", "Draft_Team", "Player", "College")
        tbls2 <- tbls[[1]] %>%
            select(2:5) %>% 
            filter(Pick != "Pk", Pick != "") %>%
            mutate(Draft_Year = y) %>%
            select(5, everything())
        tbls_all <- rbind(tbls_all, tbls2)
    }
    
    return(tbls_all)
}


# function that takes a url and returns a logical of true or false depeniding on
# whether the website exists or not

valid_url <- function(url_in, t=2) {
    con <- url(url_in)
    check <- suppressWarnings(try(open.connection(con, open = "rt", timeout = t),
                                  silent = T)[1])
    suppressWarnings(try(close.connection(con), silent = T))
    ifelse(is.null(check), TRUE, FALSE)
}


# function that takes a data frame and adds 'x' number of variables that equal 
# the value of that statistic for the previous 'x' number of years, given that
# 1 other variable matches in those years

prior_years_stats_simple <- function(df, stat, years = 1, match) {
    
    stat <- ifelse(is.numeric(stat), colnames(df[stat]), stat)
    z <- df
    
    for(y in years) {
        new_name <- paste0(stat, "_", y, "yr")
        z <- mutate(z, new_stat = ifelse(lag(z[[match]], y) == z[[match]],
                                         lag(z[[stat]], y), NA))
        names(z)[names(z) == "new_stat"] <- new_name
    }
    return(z)
} 


# function that is the same as above, except it can force matching on 2 values

prior_years_stats <- function(df, stat, years = 1, match = NA, match2 = NA) {
    
    if(is.na(match) && !is.na(match2)) {
        print("match2 must be NA if match is NA")
        return()
    }
    stat <- ifelse(is.numeric(stat), colnames(df[stat]), stat)
    z <- df
    
    for(y in years) {
        new_name <- paste0(stat, "_", y, "yr")
        z <- mutate(z, new_stat = if(is.na(match) && is.na(match2)) {
            lag(z[[stat]], y)
        }
        else if(is.na(match2)) {
            ifelse(lag(z[[match]], y) == z[[match]], lag(z[[stat]], y), NA)
        }
        else {
            ifelse(lag(z[[match]], y) == z[[match]], 
                   ifelse(lag(z[[match2]], y) == z[[match2]], 
                          lag(z[[stat]], y), NA), NA)
            
        })
        names(z)[names(z) == "new_stat"] <- new_name
    }
    return(z)
}


# function that takes a formula, a dataframe, and the dependent variable of the 
# model as a string, and runs the model and stores the evaluations in a dataframe,
# including analysis via k fold cross validation

calc_model_stats <- function(formula, model_data, depVar) {
    
    lmmod <- lm(formula, model_data)
    mod_summary <- summary(lmmod)
    
    col_index <- which(colnames(model_data) == depVar)
    
    RSE <- sigma(lmmod)
    error_rate <- sigma(lmmod)/mean(model_data[[col_index]], na.rm = TRUE)
    
    tvalues <- mod_summary$coefficients[ , 3]
    tvalues <- tvalues[-c(1)]
    pvalues <- mod_summary$coefficients[ , 4]
    pvalues <- pvalues[-c(1)]
    
    model_stats <- data.frame(matrix(0, nrow = 1, ncol = 17))
    names(model_stats) <- c("Model", "NumVar", "tVV1", "tVV2", "tVV3", "tVV4",
                            "tVV5", "pVV1", "pVV2", "pvv3", "pVV4", "pVV5", 
                            "RSE", "ErrRate", "RMSE", "Rsquared", "MAE")
    
    formula2 <- paste0(as.character(formula)[2], "~", as.character(formula[3]))
    model_stats["Model"][[1]] <- formula2
    model_stats["NumVar"][[1]] <- length(tvalues)
    model_stats["RSE"][[1]] <- RSE
    model_stats["ErrRate"][[1]] <- error_rate
    
    length(tvalues) <- 5
    count <- 3
    for(x in tvalues) {
        model_stats[count][[1]] <- x
        count <- count + 1
    }
    
    length(pvalues) <- 5
    count <- 8
    for(x in pvalues) {
        model_stats[count][[1]] <- x
        count <- count + 1
    }
    
    # repeated k-fold cross validation
    
    set.seed(10)
    train.control <- trainControl(method = "repeatedcv", number = 10, repeats = 3)
    crossval <- train(formula, data = model_data, method = "lm", 
                      trControl = train.control, na.action = na.omit)
    
    model_stats["RMSE"][[1]] <- crossval$results[ , 2]
    model_stats["Rsquared"][[1]] <- crossval$results[ , 3]
    model_stats["MAE"][[1]] <- crossval$results[ , 4]
    
    return(model_stats)
}


# function that works the same as the above, except that it doesn't report
# coefficients of the variables, and can take a model with any number of variables

calc_model_stats_unlimit <- function(formula, model_data, depVar) {
    
    lmmod <- lm(formula, model_data)
    mod_summary <- summary(lmmod)
    
    col_index <- which(colnames(model_data) == depVar)
    
    RSE <- sigma(lmmod)
    error_rate <- sigma(lmmod)/mean(model_data[[col_index]], na.rm = TRUE)
    
    tvalues <- mod_summary$coefficients[ , 3]
    
    model_stats <- data.frame(matrix(0, nrow = 1, ncol = 7))
    names(model_stats) <- c("Model", "NumVar", "RSE", "ErrRate", "RMSE", 
                            "Rsquared", "MAE")
    
    formula2 <- paste0(as.character(formula)[2], "~", as.character(formula[3]))
    model_stats["Model"][[1]] <- formula2
    model_stats["NumVar"][[1]] <- length(tvalues) - 1
    model_stats["RSE"][[1]] <- RSE
    model_stats["ErrRate"][[1]] <- error_rate
    
    
    # repeated k-fold cross validation
    
    set.seed(10)
    train.control <- trainControl(method = "repeatedcv", number = 10, repeats = 3)
    crossval <- train(formula, data = model_data, method = "lm", 
                      trControl = train.control, na.action = na.omit)
    
    model_stats["RMSE"][[1]] <- crossval$results[ , 2]
    model_stats["Rsquared"][[1]] <- crossval$results[ , 3]
    model_stats["MAE"][[1]] <- crossval$results[ , 4]
    
    return(model_stats)
}


# function that takes any number of models as its arguments, followed by the 
# last 2 arguments being the data frame and the dependent variable (as a string)
# to run the models on
# designed to be used with either of the calc_model_stats functions

run_models <- function(...) {
    
    to_run <- list(...)
    df <- to_run[[length(to_run) - 1]]
    depVar <- to_run[[length(to_run)]]
    to_run[length(to_run)] <- NULL
    to_run[length(to_run)] <- NULL
    
    
    model_results <- data.frame()
    for(x in to_run) {
        results <- calc_model_stats_unlimit(x, df, depVar)
        model_results <- rbind(model_results, results)
    }
    
    return(model_results)
}


# function that calculates projected wins for every team in the upcoming season.
# it takes a dataframe, year, and linear model as arguments

project_WinPct <- function(df, year, lmmod) {
    
    # identify expansion teams and their average wins
    df <- df %>%
        mutate(Expansion = ifelse(Team != lag(Team) & Year != 1987, TRUE, FALSE))
    expansion_avg <- mean(df[df$Expansion == TRUE, "WinPct"])
    
    df2 <- df %>% filter(Year %in% year) %>%
        mutate(Proj_WinPct = ifelse(!is.na(MOV_1yr), 
                                    predict(lmmod, newdata = ., type = "response"), 
                                    expansion_avg))
    
    return(df2)
}


# function that projects win shares and minutes for each player, using the best 
# model for each player, given how many years they've played. it takes the 
# upcoming year and a dataframe as arguments

plyr_projections <- function(df, year) {
    
    df2 <- df %>%
        filter(Year %in% year) %>% 
        mutate(Proj_WS48 = case_when(Exp >= 5 ~ predict(lmmod_ws5, newdata = ., type = "response"), 
                                     Exp == 4 ~ predict(lmmod_ws4, newdata = ., type = "response"),
                                     Exp == 3 ~ predict(lmmod_ws3, newdata = ., type = "response"), 
                                     Exp == 2 ~ predict(lmmod_ws2, newdata = ., type = "response"), 
                                     Exp == 1 ~ predict(lmmod_ws1, newdata = ., type = "response"), 
                                     Exp == 0 ~ predict(lmmod_ws0, newdata = ., type = "response")), 
               Proj_Min = case_when(Exp >= 5 ~ predict(lmmod_min5, newdata = ., type = "response"), 
                                    Exp == 4 ~ predict(lmmod_min4, newdata = ., type = "response"),
                                    Exp == 3 ~ predict(lmmod_min3, newdata = ., type = "response"), 
                                    Exp == 2 ~ predict(lmmod_min2, newdata = ., type = "response"), 
                                    Exp == 1 ~ predict(lmmod_min1, newdata = ., type = "response"), 
                                    Exp == 0 ~ predict(lmmod_min0, newdata = ., type = "response")), 
               Proj_allnba = case_when(Exp >= 4 ~ predict(lmmod_allnba4, newdata = ., type = "response"), 
                                       Exp == 3 ~ predict(lmmod_allnba3, newdata = ., type = "response"),
                                       Exp == 2 ~ predict(lmmod_allnba2, newdata = ., type = "response"),
                                       Exp == 1 ~ predict(lmmod_allnba1, newdata = ., type = "response"),
                                       Exp == 0 ~ 0))
    
    return(df2)
}


# function that takes a dataframe as an argument and replaces team names with 
# team abbreviations

rename_teams <- function(df) {
    
    df2 <- df %>%
        mutate(Team = case_when(Team == "Atlanta Hawks" ~ "ATL", 
                                Team == "Boston Celtics" ~ "BOS", 
                                Team == "Brooklyn Nets" ~ "BRK", 
                                Team == "Charlotte Hornets" ~ "CHO", 
                                Team == "Chicago Bulls" ~ "CHI", 
                                Team == "Cleveland Cavaliers" ~ "CLE", 
                                Team == "Dallas Mavericks" ~ "DAL", 
                                Team == "Denver Nuggets" ~ "DEN", 
                                Team == "Detroit Pistons" ~ "DET", 
                                Team == "Golden State Warriors" ~ "GSW", 
                                Team == "Houston Rockets" ~ "HOU", 
                                Team == "Indiana Pacers" ~ "IND", 
                                Team == "Los Angeles Clippers" ~ "LAC", 
                                Team == "Los Angeles Lakers" ~ "LAL", 
                                Team == "Memphis Grizzlies" ~ "MEM", 
                                Team == "Miami Heat" ~ "MIA", 
                                Team == "Milwaukee Bucks" ~ "MIL", 
                                Team == "Minnesota Timberwolves" ~ "MIN", 
                                Team == "New Orleans Pelicans" ~ "NOP", 
                                Team == "New York Knicks" ~ "NYK", 
                                Team == "Oklahoma City Thunder" ~ "OKC", 
                                Team == "Orlando Magic" ~ "ORL", 
                                Team == "Philadelphia 76ers" ~ "PHI", 
                                Team == "Phoenix Suns" ~ "PHO", 
                                Team == "Portland Trail Blazers" ~ "POR", 
                                Team == "Sacramento Kings" ~ "SAC", 
                                Team == "San Antonio Spurs" ~ "SAS", 
                                Team == "Toronto Raptors" ~ "TOR", 
                                Team == "Utah Jazz" ~ "UTA", 
                                Team == "Washington Wizards" ~ "WAS", 
                                TRUE ~ Team))
    return(df2)
}


# function that adds a new column(s) with career totals for given stat(s)
# up to and including that season for each player for each season

add_up_stats <- function(df, stat) {
    
    years <- c(25:1)
    
    for(x in stat) {
        x <- ifelse(is.numeric(x), colnames(df[x]), x)
        new_name <- paste0("Cum_", x) 
        
        df <- df %>%
            mutate(total = .[[x]])
        
        for(y in years) {
            df <- df %>%
                mutate(total = case_when(lag(Player, y) == Player & lag(Birthdate, y) == Birthdate ~ total + lag(.[[x]], y), 
                                         TRUE ~ total))
        }
        
        names(df)[names(df) == "total"] <- new_name
        
    }
    
    return(df)
}









########################### TEST MODELS ############################

setwd(dirname(rstudioapi::getActiveDocumentContext()$path))
all_stats_calc <- read.csv("all_stats (1980-2020).csv")

all_stats_calc <- prior_years_stats(all_stats_calc, "AllNBA", c(1:5), "Player", "Birthdate")
all_stats_calc <- prior_years_stats(all_stats_calc, "AllDef", c(1:5), "Player", "Birthdate")
all_stats_calc <- prior_years_stats(all_stats_calc, "MVP_Share", c(1:5), "Player", "Birthdate")
all_stats_calc <- prior_years_stats(all_stats_calc, "DPOY_Share", c(1:5), "Player", "Birthdate")
all_stats_calc <- prior_years_stats(all_stats_calc, "WS", c(1:5), "Player", "Birthdate")


test <- run_models(AllNBA ~ Prev_AllNBA + WS + Age, 
                   AllNBA ~ Prev_AllNBA, 
                   AllNBA ~ Prev_AllNBA + WS, 
                   AllNBA ~ Prev_AllNBA + WS + Exp, 
                   AllNBA ~ Prev_AllNBA + Exp, 
                   AllNBA ~ Prev_AllNBA + Age, 
                   AllNBA ~ Prev_AllNBA + WS + Age + Exp, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Exp, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + WS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + Exp, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + WS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Exp + WS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + Exp + WS, 
                   AllNBA ~ WS + Age, 
                   AllNBA ~ WS, 
                   AllNBA ~ WS + Exp, 
                   AllNBA ~ Exp, 
                   AllNBA ~ Age, 
                   AllNBA ~ WS + Age + Exp, 
                   AllNBA ~ AllNBA_1yr + Age, 
                   AllNBA ~ AllNBA_1yr + Exp, 
                   AllNBA ~ AllNBA_1yr + WS, 
                   AllNBA ~ AllNBA_1yr + Age + Exp, 
                   AllNBA ~ AllNBA_1yr + Age + WS, 
                   AllNBA ~ AllNBA_1yr + Exp + WS, 
                   AllNBA ~ AllNBA_1yr + Age + Exp + WS, 
                   AllNBA ~ Cum_AS + WS + Age, 
                   AllNBA ~ Cum_AS, 
                   AllNBA ~ Cum_AS + WS, 
                   AllNBA ~ Cum_AS + WS + Exp, 
                   AllNBA ~ Cum_AS + Exp, 
                   AllNBA ~ Cum_AS + Age, 
                   AllNBA ~ Cum_AS + WS + Age + Exp, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + Age, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + Exp, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + WS, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + Age + Exp, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + Age + WS, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + Exp + WS, 
                   AllNBA ~ Cum_AS + AllNBA_1yr + Age + Exp + WS, 
                   AllNBA ~ Prev_AllNBA + WS + Age + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + WS + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + WS + Exp + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + Exp + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + Age + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + WS + Age + Exp + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Exp + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + WS + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + Exp + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + WS + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Exp + WS + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + AllNBA_1yr + Age + Exp + WS + Cum_AS, 
                   AllNBA ~ Prev_AllNBA + Prev_AllDef + Prev_AllRook + Cum_AS + Prev_MVP_Share + Prev_DPOY_Share, 
                   all_stats_calc, "AllNBA")

test3 <- lm(AllNBA ~ Prev_AllNBA + Prev_AllDef + Prev_AllRook + Cum_AS + Prev_MVP_Share + Prev_DPOY_Share + Exp, all_stats_calc)

########################### ALL STATS (1980-2020) ############################

setwd(dirname(rstudioapi::getActiveDocumentContext()$path))
all_player_stats <- read.csv("all_player_stats.csv")

all_team_stats_clean <- read.csv("all_team_stats_clean.csv")
draft_results_clean <- read.csv("draft_results_clean.csv")
new_rosters_clean <- read.csv("2021_rosters_clean.csv")
allNBA_teams_clean <- read.csv("allNBA_teams_clean.csv")
awards_clean <- read.csv("awards_clean.csv")
alldefense_teams_clean <- read.csv("alldefense_teams_clean.csv")
allrookie_teams_clean <- read.csv("allrookie_teams_clean.csv")
finals_MVPs_clean <- read.csv("finals_MVPs_clean.csv")
ASG_MVPs_clean <- read.csv("ASG_MVPs_clean.csv")
all_playoff_stats <- read.csv("all_playoff_stats.csv")
allstars_clean <- read.csv("allstars_clean.csv")

allstars_clean <- allstars_clean %>%
    select(Year, Player, AS)

all_stats <- all_player_stats %>%
    select(-"Rk.x", -"Rk.y") %>%
    mutate(Exp = ifelse(Exp == "R", 0, Exp)) %>%
    mutate_at(vars(Player:VORP), as.character) %>%
    mutate_at(vars(Year, Age:MP, Exp, GS:VORP), as.numeric) %>%
    mutate_at(vars(College), gsub, pattern = "University of California, Irvine", replacement = "University of California Irvine") %>%
    mutate_at(vars(College), gsub, pattern = ".*, ", replacement = "") %>%
    mutate(Team = case_when(Team == "NJN" ~ "BRK", 
                            Team == "SEA" ~ "OKC", 
                            Team == "WSB" ~ "WAS", 
                            Team == "VAN" ~ "MEM", 
                            Team == "NOH" ~ "NOP", 
                            Team == "NOK" ~ "NOP", 
                            Team == "CHA" ~ "CHO", 
                            Team == "CHH" ~ "NOP", 
                            Team == "KCK" ~ "SAC", 
                            Team == "SDC" ~ "LAC", 
                            TRUE ~ Team), 
           Player = case_when(Player == "Gary Payton" & Year >= 2010 ~ "Gary Payton Jr.", 
                              Player == "Patrick Ewing" & Year >= 2005 ~ "Patrick Ewing Jr.", 
                              TRUE ~ Player)) %>%
    merge(draft_results_clean, by = c("Player", "College"), all.x = TRUE) %>%
    merge(new_rosters_clean, by = c("Player", "Birthdate", "Year", "Age", "Pick", 
                                    "Team", "Exp"), all = TRUE) %>%
    mutate_at(vars(Player), gsub, pattern = "\\s+\\s+\\(TW\\)", replacement = "") %>%
    merge(allNBA_teams_clean, by = c("Player", "Year"), all.x = TRUE) %>%
    mutate(PER = ifelse(is.na(PER), 0, PER), 
           WS = ifelse(is.na(WS), 0, WS), 
           Pick = ifelse(is.na(Pick), 65, Pick), 
           Tm = ifelse(is.na(Tm), 0, Tm)) %>%
    rename(AllNBA = Tm) %>%
    group_by(Player, Birthdate, Year, Age, Pick, Exp) %>%
    summarise(Teams = paste0(first(Team), 
                            ifelse(is.na(nth(Team, 2)), "", paste0("-", nth(Team, 2))), 
                            ifelse(is.na(nth(Team, 3)), "", paste0("-", nth(Team, 3))), 
                            ifelse(is.na(nth(Team, 4)), "", paste0("-", nth(Team, 4))), 
                            ifelse(is.na(nth(Team, 5)), "", paste0("-", nth(Team, 5)))), 
              Team = first(Team), 
              NumTeams = n(), 
              PER = weighted.mean(PER, MP), 
              USG = weighted.mean(USG., MP), 
              OBPM = weighted.mean(OBPM, MP), 
              DBPM = weighted.mean(DBPM, MP), 
              BPM = weighted.mean(BPM, MP), 
              VORP = weighted.mean(VORP, MP), 
              OREBp = weighted.mean(ORB., MP), 
              DREBp = weighted.mean(DRB., MP), 
              REBp = weighted.mean(TRB., MP), 
              ASTp = weighted.mean(AST., MP), 
              STLp = weighted.mean(STL., MP), 
              BLKp = weighted.mean(BLK., MP), 
              TOVp = weighted.mean(TOV., MP), 
              G = sum(G), 
              MP = sum(MP), 
              GS = sum(GS), 
              FGM = sum(FG), 
              FGA = sum(FGA), 
              FGM3 = sum(X3P),
              FGA3 = sum(X3PA), 
              FGM2 = sum(X2P), 
              FGA2 = sum(X2PA), 
              FTM = sum(FT), 
              FTA = sum(FTA),
              OREB = sum(ORB), 
              DREB = sum(DRB), 
              REB = sum(TRB), 
              AST = sum(AST), 
              STL = sum(STL), 
              BLK = sum(BLK), 
              TOV = sum(TOV), 
              PF = sum(PF), 
              PTS = sum(PTS), 
              OWS = sum(OWS), 
              DWS = sum(DWS), 
              WS = sum(WS), 
              AllNBA = first(AllNBA)) %>%
    merge(all_team_stats_clean, by = c("Team", "Year"), all.x = TRUE) %>%
    rename(GP = G.x, 
           Team_Gm = G.y, 
           Delete = Team, 
           Team = Teams) %>%
    merge(awards_clean, by = c("Player", "Year", "Age"), all.x = TRUE) %>%
    merge(allrookie_teams_clean, by = c("Player", "Year"), all.x = TRUE) %>%
    rename(AllRook = Tm) %>%
    merge(alldefense_teams_clean, by = c("Player", "Year"), all.x = TRUE) %>%
    rename(AllDef = Tm) %>%
    merge(finals_MVPs_clean, by = c("Player", "Year", "Age"), all.x = TRUE, all.y = TRUE) %>%
    merge(ASG_MVPs_clean, by = c("Player", "Year"), all.x = TRUE, all.y = TRUE) %>%
    merge(all_playoff_stats, by = c("Player", "Year", "Age", "Birthdate"), all.x = TRUE, all.y = TRUE) %>%
    merge(allstars_clean, by = c("Player", "Year"), all.x = TRUE) %>%
    arrange(Player, Birthdate, Year) %>%
    mutate_at(vars(OWS:WS, PER:TOVp), round, 1) %>%
    mutate_at(vars(MVP_Share, MIP_Share, DPOY_Share, ROY_Share, SM_Share), round, 3) %>%
    mutate(Team = ifelse(is.na(Team), pTeam, Team), 
           Pick = ifelse(is.na(Pick) & lag(Player) == Player & lag(Birthdate) == Birthdate, 
                         lag(Pick), Pick), 
           Exp = ifelse(is.na(Exp) & lag(Player) == Player & lag(Birthdate) == Birthdate, 
                         lag(Exp) + 1, Exp), 
           Pick = ifelse(is.na(Pick) & lead(Player) == Player & lead(Birthdate) == Birthdate, 
                         lead(Pick), Pick), 
           Exp = ifelse(is.na(Exp) & lead(Player) == Player & lead(Birthdate) == Birthdate, 
                        lead(Exp) - 1, Exp), 
           YrsOff = case_when(lag(Player) == Player & lag(Birthdate) == Birthdate ~ Year - lag(Year) - 1, 
                              TRUE ~ 0)) %>%
    select(Player, Birthdate, Pick, Year, YrsOff, Age, Exp, Team, Team_Gm, GP, GS, MP, PTS, 
           FGM:PF, OWS:WS, PER, OREBp:TOVp, USG:VORP, pGP:pVORP, AS, AllNBA, AllDef, AllRook, 
           MVP_Rk, MVP_Share, DPOY_Rk, DPOY_Share, ROY_Rk, ROY_Share, MIP_Rk, MIP_Share, SM_Rk, 
           SM_Share, FinalsMVP, ASG_MVP, WinPct:NRtg) %>%
    arrange(Team, Year) %>%
    mutate_at(vars(GP:ASG_MVP), ~ ifelse(is.na(.) & Year != 2021, 0, .)) %>%
    mutate_at(vars(Team_Gm, WinPct:NRtg), ~ ifelse(is.na(.) & Year != 2021 & lag(Team) == Team, lag(.), .)) %>%
    # filter(Year >= 1990) %>%
    arrange(Player, Birthdate, Year)


############################# ADD NEW VARIABLES ###############################

all_stats_calc <- all_stats %>%
    mutate(AllNBA1 = ifelse(AllNBA == 1, 1, 0), 
           AllNBA2 = ifelse(AllNBA == 2, 1, 0), 
           AllNBA3 = ifelse(AllNBA == 3, 1, 0), 
           AllDef1 = ifelse(AllDef == 1, 1, 0), 
           AllDef2 = ifelse(AllDef == 2, 1, 0), 
           AllRook1 = ifelse(AllRook == 1, 1, 0), 
           AllRook2 = ifelse(AllRook == 2, 1, 0), 
           AllNBAV = 5*AllNBA1 + 3*AllNBA2 + 1*AllNBA3, 
           AllDefV = 3*AllDef1 + 1*AllDef2, 
           AllRookV = 3*AllRook1 + 1*AllRook2, 
           AllNBA = ifelse(AllNBA > 0, 1, 0), 
           AllDef = ifelse(AllDef > 0, 1, 0), 
           AllRook = ifelse(AllRook > 0, 1, 0)) %>%
    add_up_stats(c("GP", "GS", "MP", "PTS", "FGM", "FGA", "FGM3", "FGA3", "FGM2", 
                   "FGA2", "FTM", "FTA", "OREB", "DREB", "REB", "AST", "STL", "BLK", 
                   "TOV", "PF", "OWS", "DWS", "WS", "pGP", "pGS", "pMP", "pPTS", 
                   "pFGM", "pFGA", "pFGM3", "pFGA3", "pFGM2", "pFGA2", "pFTM", 
                   "pFTA", "pOREB", "pDREB", "pREB", "pAST", "pSTL", "pBLK", "pTOV", 
                   "pPF", "pOWS", "pDWS", "pWS", "AS", "AllNBA", "AllNBA1", "AllNBA2", 
                   "AllNBA3", "AllNBAV", "AllDef", "AllDef1", "AllDef2", "AllDefV", 
                   "AllRook", "AllRook1", "AllRook2", "AllRookV", "MVP_Share", "DPOY_Share", 
                   "ROY_Share", "MIP_Share", "SM_Share", "FinalsMVP", "ASG_MVP")) %>%
    mutate(MP_g = ifelse(GP == 0, 0, MP / GP), 
           PTS_g = ifelse(GP == 0, 0, PTS / GP), 
           FGM_g = ifelse(GP == 0, 0, FGM / GP), 
           FGA_g = ifelse(GP == 0, 0, FGA / GP), 
           FGM3_g = ifelse(GP == 0, 0, FGM3 / GP), 
           FGA3_g = ifelse(GP == 0, 0, FGA3 / GP), 
           FGM2_g = ifelse(GP == 0, 0, FGM2 / GP), 
           FGA2_g = ifelse(GP == 0, 0, FGA2 / GP), 
           FTM_g = ifelse(GP == 0, 0, FTM / GP), 
           FTA_g = ifelse(GP == 0, 0, FTA / GP), 
           OREB_g = ifelse(GP == 0, 0, OREB / GP), 
           DREB_g = ifelse(GP == 0, 0, DREB / GP), 
           REB_g = ifelse(GP == 0, 0, REB / GP), 
           AST_g = ifelse(GP == 0, 0, AST / GP), 
           STL_g = ifelse(GP == 0, 0, STL / GP), 
           BLK_g = ifelse(GP == 0, 0, BLK / GP), 
           TOV_g = ifelse(GP == 0, 0, TOV / GP), 
           PF_g = ifelse(GP == 0, 0, PF / GP), 
           OWS_g = ifelse(GP == 0, 0, OWS / GP), 
           DWS_g = ifelse(GP == 0, 0, DWS / GP), 
           WS_g = ifelse(GP == 0, 0, WS / GP), 
           PTS_36 = ifelse(MP == 0, 0, PTS / MP * 36), 
           FGM_36 = ifelse(MP == 0, 0, FGM / MP * 36), 
           FGA_36 = ifelse(MP == 0, 0, FGA / MP * 36), 
           FGM3_36 = ifelse(MP == 0, 0, FGM3 / MP * 36), 
           FGA3_36 = ifelse(MP == 0, 0, FGA3 / MP * 36), 
           FGM2_36 = ifelse(MP == 0, 0, FGM2 / MP * 36), 
           FGA2_36 = ifelse(MP == 0, 0, FGA2 / MP * 36), 
           FTM_36 = ifelse(MP == 0, 0, FTM / MP * 36), 
           FTA_36 = ifelse(MP == 0, 0, FTA / MP * 36), 
           OREB_36 = ifelse(MP == 0, 0, OREB / MP * 36), 
           DREB_36 = ifelse(MP == 0, 0, DREB / MP * 36), 
           REB_36 = ifelse(MP == 0, 0, REB / MP * 36), 
           AST_36 = ifelse(MP == 0, 0, AST / MP * 36), 
           STL_36 = ifelse(MP == 0, 0, STL / MP * 36), 
           BLK_36 = ifelse(MP == 0, 0, BLK / MP * 36), 
           TOV_36 = ifelse(MP == 0, 0, TOV / MP * 36), 
           PF_36 = ifelse(MP == 0, 0, PF / MP * 36), 
           OWS_48 = ifelse(MP == 0, 0, OWS / MP * 48), 
           DWS_48 = ifelse(MP == 0, 0, DWS / MP * 48), 
           WS_48 = ifelse(MP == 0, 0, WS / MP * 48), 
           FGp = ifelse(FGA == 0, 0, FGM / FGA), 
           FG3p = ifelse(FGA3 == 0, 0, FGM3 / FGA3),  
           FG2p = ifelse(FGA2 == 0, 0, FGM2 / FGA2), 
           FTp = ifelse(FTA == 0, 0, FTM / FTA), 
           EFGp = ifelse(FGA == 0, 0, (FGM + 0.5 * FGM3) / FGA), 
           TSp = ifelse(FGA + FTA == 0, 0, PTS / (2 * (FGA + 0.44 * FTA))), 
           FGA3r = ifelse(FGA == 0, 0, FGA3 / FGA), 
           FTr = ifelse(FGA == 0, 0, FTA / FGA), 
           pMP_g = ifelse(pGP == 0, 0, pMP / pGP), 
           pPTS_g = ifelse(pGP == 0, 0, pPTS / pGP), 
           pPFGM_g = ifelse(pGP == 0, 0, pFGM / pGP), 
           pFGA_g = ifelse(pGP == 0, 0, pFGA / pGP), 
           pFGM3_g = ifelse(pGP == 0, 0, pFGM3 / pGP), 
           pFGA3_g = ifelse(pGP == 0, 0, pFGA3 / pGP), 
           pFGM2_g = ifelse(pGP == 0, 0, pFGM2 / pGP), 
           pFGA2_g = ifelse(pGP == 0, 0, pFGA2 / pGP), 
           pFTM_g = ifelse(pGP == 0, 0, pFTM / pGP), 
           pFTA_g = ifelse(pGP == 0, 0, pFTA / pGP), 
           pOREB_g = ifelse(pGP == 0, 0, pOREB / pGP), 
           pDREB_g = ifelse(pGP == 0, 0, pDREB / pGP), 
           pREB_g = ifelse(pGP == 0, 0, pREB / pGP), 
           pAST_g = ifelse(pGP == 0, 0, pAST / pGP), 
           pSTL_g = ifelse(pGP == 0, 0, pSTL / pGP), 
           pBLK_g = ifelse(pGP == 0, 0, pBLK / pGP), 
           pTOV_g = ifelse(pGP == 0, 0, pTOV / pGP), 
           pPF_g = ifelse(pGP == 0, 0, pPF / pGP), 
           pOWS_g = ifelse(pGP == 0, 0, pOWS / pGP), 
           pDWS_g = ifelse(pGP == 0, 0, pDWS / pGP), 
           pWS_g = ifelse(pGP == 0, 0, pWS / pGP), 
           pPTS_36 = ifelse(pMP == 0, 0, pPTS / pMP * 36), 
           pFGM_36 = ifelse(pMP == 0, 0, pFGM / pMP * 36), 
           pFGA_36 = ifelse(pMP == 0, 0, pFGA / pMP * 36), 
           pFGM3_36 = ifelse(pMP == 0, 0, pFGM3 / pMP * 36), 
           pFGA3_36 = ifelse(pMP == 0, 0, pFGA3 / pMP * 36), 
           pFGM2_36 = ifelse(pMP == 0, 0, pFGM2 / pMP * 36), 
           pFGA2_36 = ifelse(pMP == 0, 0, pFGA2 / pMP * 36), 
           pFTM_36 = ifelse(pMP == 0, 0, pFTM / pMP * 36), 
           pFTA_36 = ifelse(pMP == 0, 0, pFTA / pMP * 36), 
           pOREB_36 = ifelse(pMP == 0, 0, pOREB / pMP * 36), 
           pDREB_36 = ifelse(pMP == 0, 0, pDREB / pMP * 36), 
           pREB_36 = ifelse(pMP == 0, 0, pREB / pMP * 36), 
           pAST_36 = ifelse(pMP == 0, 0, pAST / pMP * 36), 
           pSTL_36 = ifelse(pMP == 0, 0, pSTL / pMP * 36), 
           pBLK_36 = ifelse(pMP == 0, 0, pBLK / pMP * 36), 
           pTOV_36 = ifelse(pMP == 0, 0, pTOV / pMP * 36), 
           pPF_36 = ifelse(pMP == 0, 0, pPF / pMP * 36), 
           pOWS_48 = ifelse(pMP == 0, 0, pOWS / pMP * 48), 
           pDWS_48 = ifelse(pMP == 0, 0, pDWS / pMP * 48), 
           pWS_48 = ifelse(pMP == 0, 0, pWS / pMP * 48), 
           pFGp = ifelse(pFGA == 0, 0, pFGM / pFGA), 
           pFG3p = ifelse(pFGA3 == 0, 0, pFGM3 / pFGA3), 
           pFG2p = ifelse(pFGA2 == 0, 0, pFGM2 / pFGA2), 
           pFTp = ifelse(pFTA == 0, 0, pFTM / pFTA), 
           pEFGp = ifelse(pFGA == 0, 0, (pFGM + 0.5 * pFGM3) / pFGA), 
           pTSp = ifelse(pFGA + pFTA == 0, 0, pPTS / (2 * (pFGA + 0.44 * pFTA))), 
           pFGA3r = ifelse(pFGA == 0, 0, pFGA3 / pFGA), 
           pFTr = ifelse(pFGA == 0, 0, pFTA / pFGA), 
           Prev_AllNBAV = Cum_AllNBAV - AllNBAV, 
           Prev_AllNBA = Cum_AllNBA - AllNBA, 
           Prev_AllNBA1 = Cum_AllNBA1 - AllNBA1, 
           Prev_AllNBA2 = Cum_AllNBA2 - AllNBA2, 
           Prev_AllNBA3 = Cum_AllNBA3 - AllNBA3, 
           Prev_AllDefV = Cum_AllDefV - AllDefV, 
           Prev_AllDef = Cum_AllDef - AllDef, 
           Prev_AllDef1 = Cum_AllDef1 - AllDef1, 
           Prev_AllDef2 = Cum_AllDef2 - AllDef2, 
           Prev_AllRookV = Cum_AllRookV - AllRookV, 
           Prev_AllRook = Cum_AllRook - AllRook, 
           Prev_AllRook1 = Cum_AllRook1 - AllRook1, 
           Prev_AllRook2 = Cum_AllRook2 - AllRook2, 
           Prev_MVP_Share = Cum_MVP_Share - MVP_Share, 
           Prev_DPOY_Share = Cum_DPOY_Share - DPOY_Share, 
           Prev_ROY_Share = Cum_ROY_Share - ROY_Share, 
           Prev_MIP_Share = Cum_MIP_Share - MIP_Share, 
           Prev_SM_Share = Cum_SM_Share - SM_Share, 
           Prev_FinalsMVP = Cum_FinalsMVP - FinalsMVP) %>%
    mutate_at(vars(MP_g:WS_48, pMP_g:pWS_48), round, 1) %>%
    mutate_at(vars(FGp:FTr, pFGp:pFTr), round, 3) %>%
    select(Player:FGA, FGp, FGM3:FGA3, FG3p, FGM2:FGA2, FG2p, FTM:FTA, FTp:FTr, 
           OREB:WS, MP_g:WS_48, PER:VORP, Cum_GP:Cum_WS, pGP:pFGA, pFGp, pFGM3:pFGA3, 
           pFG3p, pFGM2:pFGA2, pFG2p, pFTM:pFTA, pFTp:pFTr, pOREB:pWS, pMP_g:pWS_48, 
           pPER:pVORP, Cum_pGP:Cum_pWS, AS, Cum_AS, AllNBAV, AllNBA, AllNBA1:AllNBA3, Cum_AllNBAV, Cum_AllNBA, 
           Cum_AllNBA1:Cum_AllNBA3, Prev_AllNBAV:Prev_AllNBA3, AllDefV, AllDef, AllDef1:AllDef2, Cum_AllDefV, 
           Cum_AllDef, Cum_AllDef1:Cum_AllDef2, Prev_AllDefV:Prev_AllDef2, AllRookV, AllRook, AllRook1:AllRook2, 
           Cum_AllRookV, Cum_AllRook, Cum_AllRook1:Cum_AllRook2, Prev_AllRookV:Prev_AllRook2, MVP_Rk:MVP_Share, 
           Cum_MVP_Share, Prev_MVP_Share, DPOY_Rk:DPOY_Share, Cum_DPOY_Share, Prev_DPOY_Share, 
           ROY_Rk:ROY_Share, Cum_ROY_Share, Prev_ROY_Share, MIP_Rk:MIP_Share, Cum_MIP_Share, Prev_MIP_Share, 
           SM_Rk:SM_Share, Cum_SM_Share, Prev_SM_Share, FinalsMVP, Cum_FinalsMVP, Prev_FinalsMVP, 
           ASG_MVP, Cum_ASG_MVP, WinPct:NRtg)


write.csv(all_stats_calc, 
          "C:\\Users\\rytwin\\Documents\\R_files\\all_stats (1980-2020).csv", 
          row.names = FALSE)

# added a prior for WS/48min of:
# average of WS/48min for the entire dataset
# over 48 minutes

# mutate(WS48 = (WS / MP) * 48) %>%
# mutate(WS48adj = ((mean(.$WS48, na.rm = TRUE) * (48/48)) + WS) / ((MP + 48)) * 48) %>%
# mutate_at(vars(WS48, WS48adj), round, 3) %>%
# mutate_at(vars(MinPG), round, 1) %>%
# mutate_at(vars(MP), round, 0)


############################# DATA SCRAPING ############################
############################# AWARDS ###################################

seasons <- c(2021:2022)

awards <- data.frame()

for(val in seasons) {
    season_url <- paste0("https://www.basketball-reference.com/awards/awards_",
                         val, ".html")
    if(val > 1987 | val == 1986) {
        table_ids <- c(1:5)
    }
    else if(val > 1983 | val == 1987 ) {
        table_ids <- c(1:4)
    }
    else if(val == 1983) {
        table_ids <- c(1:3)
    }
    else {
        table_ids <- c(1:2)
    }
    results <- scrape_bballref(season_url, table_ids)
    results <- lapply(results, mutate, Year = val)
    results[[1]] <- mutate(results[[1]], type = "MVP")
    results[[2]] <- mutate(results[[2]], type = "ROY")
    if(length(table_ids) >= 3) {
        results[[3]] <- mutate(results[[3]], type = "DPOY")
    }
    if(length(table_ids) >= 4) {
        results[[4]] <- mutate(results[[4]], type = "6M")
    }
    if(length(table_ids) >= 5) {
    results[[5]] <- mutate(results[[5]], type = "MIP")
    }
    results <- lapply(results, select, c(Year, Player, Age, type, Rank, Share))
    for(z in results) {
        awards <- rbind(awards, z)
    }
}
rm(val, season_url, z, results, table_ids)

awards_clean <- awards %>%
    pivot_wider(names_from = type, values_from = Rank:Share) %>%
    mutate_at(vars(Rank_MVP:Rank_MIP), gsub, pattern = "T", replacement = "") %>%
    mutate_at(vars(Year:Share_MIP), as.character) %>%
    mutate_at(vars(Year, Age:Share_MIP), as.numeric) %>%
    rename(MVP_Rk = Rank_MVP, 
           MVP_Share = Share_MVP, 
           MIP_Rk = Rank_MIP, 
           MIP_Share = Share_MIP, 
           SM_Rk = Rank_6M, 
           SM_Share = Share_6M, 
           ROY_Rk = Rank_ROY, 
           ROY_Share = Share_ROY, 
           DPOY_Rk = Rank_DPOY, 
           DPOY_Share = Share_DPOY)
    

write.csv(awards_clean, 
          "/Users/ryandrost/Documents/R_projects/awards_2021-2022.csv", 
          row.names = FALSE)

############################# ALL-ROOKIE TEAMS ############################


allrookie_teams <- scrape_bballref("https://www.basketball-reference.com/awards/all_rookie.html", 1)[[1]]
allrookie_teams <- allrookie_teams[!apply(allrookie_teams == "", 1, all), ]
names(allrookie_teams) <- c("Year", "Lg", "Tm", "A", "B", "C", "D", "E")

allrookie_teams_clean <- allrookie_teams %>%
    mutate_at(vars(Year:E), as.character) %>%
    mutate(Tm = case_when(Tm == "1st" ~ 1, 
                          Tm == "2nd" ~ 2)) %>%
    mutate(Year = paste0(substr(Year, 1, 2), substr(Year, 6, 7))) %>%
    mutate_at(vars(Year, Tm), as.numeric) %>%
    mutate(Year = ifelse(Year == 1900, 2000, Year)) %>%
    filter(Year >= 2021) %>%
    select(-Lg) %>%
    pivot_longer(A:E) %>%
    select(-name) %>%
    rename(Player = value)

extra <- data.frame()
count <- 1
dups <- 1
while(count <= nrow(allrookie_teams_clean)) {
    if(grepl("(T)", allrookie_teams_clean$Player[count], fixed = TRUE) == TRUE) {
        z <- data.frame(Year = allrookie_teams_clean$Year[count], 
                        Tm = allrookie_teams_clean$Tm[count], 
                        Player = allrookie_teams_clean$Player[count])
        extra <- rbind(extra, z)
        dups <- dups + 1
    }
    count <- count + 1
}

extra <- extra %>%
    mutate_at(vars(Player), gsub, pattern = ",.*", replacement = "")

allrookie_teams_clean <- allrookie_teams_clean %>%
    mutate_at(vars(Player), gsub, pattern = ".*, ", replacement = "") %>%
    mutate_at(vars(Player), gsub, pattern = "\\s+\\(T\\)", replacement = "") %>%
    rbind(extra)

rm(extra)


write.csv(allrookie_teams_clean, 
          "/Users/ryandrost/Documents/R_projects/allrookie_teams_2021-2022.csv", 
          row.names = FALSE)

############################# ALL-DEFENSE TEAMS ############################


alldefense_teams <- scrape_bballref("https://www.basketball-reference.com/awards/all_defense.html", 1)[[1]]
alldefense_teams <- alldefense_teams[!apply(allrookie_teams == "", 1, all), ]
names(alldefense_teams) <- c("Year", "Lg", "Tm", "V", "A", "B", "C", "D", "E")

alldefense_teams_clean <- alldefense_teams %>%
    mutate_at(vars(Year:E), as.character) %>%
    mutate(Tm = case_when(Tm == "1st" ~ 1, 
                          Tm == "2nd" ~ 2)) %>%
    mutate(Year = paste0(substr(Year, 1, 2), substr(Year, 6, 7))) %>%
    mutate_at(vars(Year, Tm), as.numeric) %>%
    mutate(Year = ifelse(Year == 1900, 2000, Year)) %>%
    filter(Year >= 2021) %>%
    select(-Lg) %>%
    pivot_longer(A:E) %>%
    select(-name, -V) %>%
    rename(Player = value) %>%
    mutate_at(vars(Player), gsub, pattern = "Anderson Varej\\W\\Wo", replacement = "Anderson Varej?o")

extra <- data.frame()
count <- 1
dups <- 1
while(count <= nrow(alldefense_teams_clean)) {
    if(grepl("(T)", alldefense_teams_clean$Player[count], fixed = TRUE) == TRUE) {
        z <- data.frame(Year = alldefense_teams_clean$Year[count], 
                        Tm = alldefense_teams_clean$Tm[count], 
                        Player = alldefense_teams_clean$Player[count])
        extra <- rbind(extra, z)
        dups <- dups + 1
    }
    count <- count + 1
}
rm(count, dups, z)

extra <- extra %>%
    mutate_at(vars(Player), gsub, pattern = ",.*", replacement = "")

alldefense_teams_clean <- alldefense_teams_clean %>%
    mutate_at(vars(Player), gsub, pattern = ".*, ", replacement = "") %>%
    mutate_at(vars(Player), gsub, pattern = "\\s+\\(T\\)", replacement = "") %>%
    rbind(extra)

rm(extra)

write.csv(alldefense_teams_clean, 
          "/Users/ryandrost/Documents/R_projects/alldefense_2021-2022.csv", 
          row.names = FALSE)

############################# FINALS MVPS ##############################

finals_MVPs <- scrape_bballref("https://www.basketball-reference.com/awards/finals_mvp.html", 1)[[1]]

finals_MVPs_clean <- finals_MVPs %>%
    select(Season:Age) %>%
    rename(Year = Season, 
           FinalsMVP = Lg) %>%
    mutate_at(vars(Year:Age), as.character) %>%
    mutate(Year = paste0(substr(Year, 1, 2), substr(Year, 6, 7))) %>%
    mutate(Year = ifelse(Year == 1900, 2000, Year), 
           FinalsMVP = 1) %>%
    mutate_at(vars(Year, FinalsMVP, Age), as.numeric) %>%
    filter(Year >= 2021)

write.csv(finals_MVPs_clean, 
          "/Users/ryandrost/Documents/R_projects/finals_MVPs_2021-2022.csv", 
          row.names = FALSE)

############################# ASG MVPs #####################################

ASG_MVPs <- scrape_bballref("https://www.basketball-reference.com/awards/all_star_mvp.html", 1)[[1]]

ASG_MVPs <- ASG_MVPs[-31, ]
ASG_MVPs_clean <- ASG_MVPs %>%
    select(Season:Player) %>%
    rename(Year = Season, 
           ASG_MVP = Lg) %>%
    mutate_at(vars(Year:Player), as.character) %>%
    mutate(Year = paste0(substr(Year, 1, 2), substr(Year, 6, 7))) %>%
    mutate(Year = ifelse(Year == 1900, 2000, Year), 
           ASG_MVP = 1) %>%
    mutate_at(vars(Player), gsub, pattern = "\\s\\(Tie\\)", replacement = "") %>%
    mutate_at(vars(Year, ASG_MVP), as.numeric) %>%
    filter(Year >= 2021)
    

write.csv(ASG_MVPs_clean, 
          "/Users/ryandrost/Documents/R_projects/ASG_MVPs_2021-22.csv", 
          row.names = FALSE)

############################# PLAYOFF STATS ###############################

seasons <- 2021:2022
teams <- c("ATL", "BOS", "BRK", "CHO", "CHI", "CLE", "DAL", "DEN", "DET", "GSW", 
           "HOU", "IND", "LAC", "LAL", "MEM", "MIA", "MIL", "MIN", "NOP", "NYK",
           "OKC", "ORL", "PHI", "PHO", "POR", "SAC", "SAS", "TOR", "UTA", "WAS", 
           "NJN", "SEA", "CHA", "CHH", "WSB", "VAN", "NOH", "NOK")

playoff_rosters2 <- list()
playoff_stats_tot2 <- list()
playoff_stats_adv2 <- list()
count <- 1

start_time <- Sys.time()
for(val in seasons) {
    for (y in teams) {
        team_url <- paste0("https://www.basketball-reference.com/teams/", y, 
                           "/", val, ".html")
        if(valid_url(team_url) == TRUE) {
            indexes <- ifelse(rep(val < 1997, 3), c(1, 11, 15), c(1, 8, 14))
            results <- scrape_bballref(team_url, indexes)
            playoff_rosters <- results[[1]]
            playoff_stats_tot <- results[[2]]
            playoff_stats_adv <- results[[3]]
            if(is.null(playoff_stats_adv)) {
                next
            }
            else if(ncol(playoff_stats_adv) != 27) {
                next
            }
            else {
                names(playoff_rosters)[7] <- "Nat"
                names(playoff_stats_tot)[2] <- "Player"
                names(playoff_stats_adv)[2] <- "Player"
                playoff_stats_tot <- playoff_stats_tot %>%
                    select(-c(9, 12, 15, 19))
                playoff_stats_adv <- playoff_stats_adv %>%
                    select(-c(18, 23))
                playoff_rosters2[[count]] <- playoff_rosters %>%
                    mutate(Team = y, Year = val)
                playoff_stats_tot2[[count]] <- playoff_stats_tot %>%
                    mutate(Team = y, Year = val)
                playoff_stats_adv2[[count]] <- playoff_stats_adv %>%
                    mutate(Team = y, Year = val)
                count <- count + 1
            }
        }
    }
}
end_time <- Sys.time()

end_time - start_time


playoff_rosters_df <- bind_rows(playoff_rosters2)
playoff_stats_tot_df <- bind_rows(playoff_stats_tot2)
playoff_stats_adv_df <- bind_rows(playoff_stats_adv2)

names(playoff_rosters_df)[6] <- "Birthdate"
playoff_rosters_df <- playoff_rosters_df %>%
    select(Player, Ht:Exp, Team:Year)
playoff_stats_adv_df <- playoff_stats_adv_df %>%
    select(Player:PER, "ORB%":WS, OBPM:Year)
all_playoff_stats <- playoff_stats_tot_df %>%
    select(Player:"2PA", FT:Year) %>%
    merge(playoff_rosters_df, by = c("Player", "Team", "Year"), all.x = TRUE) %>%
    merge(playoff_stats_adv_df, by = c("Player", "Team", "Year", "Age", "G", "MP")) %>%
    select(Player, Birthdate, Ht, Nat, Year, Age, Team, G, GS, MP, PTS, 
           FG:PF, OWS:WS, PER:VORP)

all_playoff_stats <- all_playoff_stats %>%
    rename(pGP = G, 
           pGS = GS, 
           pMP = MP, 
           pPTS = PTS, 
           pFGM = FG, 
           pFGA = FGA, 
           pFGM3 = '3P', 
           pFGA3 = '3PA',
           pFGM2 = '2P', 
           pFGA2 = '2PA', 
           pFTM = FT, 
           pFTA = FTA, 
           pOREB = ORB, 
           pDREB = DRB, 
           pREB = TRB, 
           pAST = AST, 
           pSTL = STL, 
           pBLK = BLK, 
           pTOV = TOV, 
           pPF = PF, 
           pOWS = OWS, 
           pDWS = DWS, 
           pWS = WS, 
           pPER = PER, 
           pOREBp = 'ORB%', 
           pDREBp = 'DRB%', 
           pREBp = 'TRB%', 
           pASTp = 'AST%', 
           pSTLp = 'STL%', 
           pBLKp = 'BLK%', 
           pTOVp = 'TOV%', 
           pUSG = 'USG%', 
           pOBPM = OBPM, 
           pDBPM = DBPM, 
           pBPM = BPM, 
           pVORP = VORP, 
           pTeam = Team) %>%
    mutate_at(vars(Player:pVORP), as.character) %>%
    mutate_at(vars(Year, Age, pGP:pVORP), as.numeric) %>%
    mutate(Player = ifelse(Player == "Patrick Ewing" & Year > 2010, "Patrick Ewing Jr.", Player))


rm(playoff_stats_tot, playoff_stats_adv, playoff_rosters, 
   playoff_stats_tot2, playoff_stats_adv2, playoff_rosters2, 
   results, count, team_url, val, y, indexes)

write.csv(all_playoff_stats, 
          "/Users/ryandrost/Documents/R_projects/playoff_stats_2021-2022.csv", 
          row.names = FALSE)


############################# ALL-STARS #####################################

allstars <- list()
count <- 1

seasons = c(2021:2022)
for(y in seasons) {
    
    url <- paste0("https://www.basketball-reference.com/allstar/NBA_", y, ".html")
    results <- scrape_bballref(url, c(2, 3))
    
    allstars[[count]] <- results[[1]] %>%
        mutate(Year = y)
    allstars[[count + 1]] <- results[[2]] %>%
        mutate(Year = y)
    
    count <- count + 2
}

allstars_clean <- bind_rows(allstars)
allstars_clean <- allstars_clean %>%
    filter(Tm != "Tm" & Tm != "Totals") %>%
    rename(Player = Starters)


injured <- character()
count <- 1
for(y in seasons) {
    url <- paste0("https://www.basketball-reference.com/allstar/NBA_", y, ".html")
    results <- read_html(url) %>%
        html_nodes("ul") %>%
        html_text()
    injured[count] <- paste0(results[14], y)
    count <- count + 1
}

injured2 <- data.frame(text = injured, Year = str_sub(injured, -4, -1)) %>%
    filter(grepl("Did not play", text))
injured3 <- injured2 %>%
    mutate(text2 = str_extract(text, ".*?Did not play")) %>%
    mutate_at(vars(text), sub, pattern = ".*?Did not play", replacement = "") %>%
    mutate(text3 = str_extract(text, ".*?Did not play")) %>%
    mutate_at(vars(text), sub, pattern = ".*?Did not play", replacement = "") %>%
    mutate(text4 = str_extract(text, ".*?Did not play")) %>%
    mutate_at(vars(text), sub, pattern = ".*?Did not play", replacement = "") %>%
    mutate(text5 = str_extract(text, ".*?Did not play")) %>%
    mutate_at(vars(text), sub, pattern = ".*?Did not play", replacement = "") %>%
    mutate(text6 = str_extract(text, ".*?Did not play")) %>%
    pivot_longer(text2:text6) %>%
    select(Year, value) %>%
    rename(Player = value) %>%
    mutate(Player = str_extract(Player, "[[:graph:]]*\\s[[:graph:]]*\\s\\([[:graph:]]*\\)\\: Did not play")) %>%
    mutate_at(vars(Player), sub, pattern = ".*\\.", replacement = "") %>%
    mutate_at(vars(Player), sub, pattern = "\\s\\(.*", replacement = "") %>%
    mutate(Player = ifelse(Year == 2015 | Year == 2016, 
                           str_extract(Player, "[[:upper:]][[:lower:]]*\\s[[:alpha:]]*"), Player)) %>%
    filter(!is.na(Player))

allstars_clean <- allstars_clean %>%
    merge(injured3, by = c("Player", "Year"), all.x = TRUE, all.y = TRUE) %>%
    mutate(AS = 1)

write.csv(allstars_clean, 
          "/Users/ryandrost/Documents/R_projects/allstars_2021-22.csv", 
          row.names = FALSE)
