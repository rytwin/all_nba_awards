library(tidyverse)
library(XML)
library(stringr)
source("functions.R")

seasons <- 1980:2023


# scrape team stat tables: total, opp total, per 100 poss, opp per 100 poss, advanced, shooting, opp shooting 
team_stats_rs <- scrape_team_stats(seasons, regular_season = TRUE)
write.csv(team_stats_rs, "data/team_stats_rs_1980-2023.csv", row.names = FALSE) 

# scrape information from franchise encyclopedia
franchise_tables <- list()
for(t in franchises) {
  team_url <- paste0("https://www.basketball-reference.com/teams/", t)
  table <- data.frame(scrape_bballref(team_url, 1))
  franchise_tables <- c(franchise_tables, list(table))
  print(t)
  Sys.sleep(5)
}

team_df <- bind_rows(franchise_tables)
names(team_df) <- colnames_franchise_encyc
team_df <- team_df %>%
  rename_teams() %>%
  mutate(year = as.integer(paste0(substr(year, 1, 2), substr(year, 6, 7))),
         year = ifelse(year == 1900, 2000, year),
         div_finish = as.integer(substr(finish, 1, 1)),
         div_teams = as.integer(substr(finish, nchar(finish), nchar(finish))),
         playoff = tolower(playoff),
         champion = case_when(playoff == "won finals" ~ 1,
                              TRUE ~ 0),
         finals = case_when(champion == 1 ~ 1,
                            playoff == "lost finals" ~ 1,
                            TRUE ~ 0),
         conf_finals = case_when(champion == 1 | finals == 1 ~ 1,
                                 grepl("conf. finals", playoff) ~ 1,
                                 TRUE ~ 0),
         second_rd = case_when(champion == 1 | finals == 1 | conf_finals == 1 ~ 1,
                               grepl("conf. semis", playoff) ~ 1,
                               TRUE ~ 0),
         playoffs = case_when(champion == 1 | finals == 1 | conf_finals == 1 | second_rd == 1 ~ 1,
                              grepl("1st rnd.", playoff) ~ 1,
                              TRUE ~ 0),
         coach = tolower(coach),
         num_coaches = str_count(coach, ",") + 1,
         start_coach = sub("\\s*\\(.*", "", coach),
         end_coach = sub(".*,(.*?)(?=\\()", "\\1", coach, perl=TRUE),
         end_coach = sub("\\s*\\(.*", "", end_coach),
         across(c(start_coach, end_coach), trimws),
         top_ws = as.numeric(gsub(".*\\((.*?)\\).*", "\\1", top_ws))) %>%
  filter(year >= 1980,
         year < 2024) %>%
  select(-c(league, w, l, srs, pace, ortg, drtg, del1, del2, finish, coach, playoff)) %>%
  mutate(across(c(start_coach, end_coach), ~ gsub("\\.\\s", "", .))) %>%
  rename_duplicate_coaches("start_coach") %>%
  select(-start_coach) %>%
  rename(start_coach = coach) %>%
  rename_duplicate_coaches("end_coach") %>%
  select(-end_coach) %>%
  rename(end_coach = coach)

write.csv(team_df, "data/franchise_encyclopedia_1980-2023.csv", row.names = FALSE) 

# merge with team stats
all_team_stats <- all_team_stats %>%
  merge(team_df, by = c("team", "year"), all = TRUE)

# scrape team ratings pages
ratings <- scrape_yearly_tables("https://www.basketball-reference.com/leagues/NBA_", seasons, 1, "_ratings.html")
names(ratings) <- colnames_team_ratings
ratings_df <- ratings %>%
  mutate(across(c(conf, div), tolower)) %>%
  select(team, year, conf, div, ortg2, drtg2, net_rtg2, mov_adj, ortg2_adj, drtg2_adj, net_rtg2_adj) %>%
  rename_teams()

write.csv(ratings_df, "data/ratings_1980-2023.csv", row.names = FALSE)

# merge with team stats
all_team_stats <- all_team_stats %>%
  merge(ratings_df, by = c("team", "year"), all = TRUE)

# scrape coach information
coaches <- scrape_yearly_tables("https://www.basketball-reference.com/leagues/NBA_", seasons, 1, "_coaches.html")
names(coaches) <- colnames_coaches
coaches_df <- coaches %>%
  rename_teams_abbrev() %>%
  mutate(coach = tolower(coach)) %>%
  select(-starts_with("del"))

check_coach_names <- coaches_df %>%
  group_by(coach, coach_exp) %>%
  summarize(count = n()) %>%
  filter(count > 1) %>%
  pull(coach)

coaches_df <- coaches_df %>%
  rename_duplicate_coaches("coach") %>%
  mutate(coach_id = paste0(substr(coach, 1, 1), sub("^[^ ]+ ", "", coach)),
         coach_id = gsub("st. jean", "stjean", coach_id)) %>%
  replace(is.na(.), 0)

write.csv(coaches_df, "data/coaches_1980-2023.csv", row.names = FALSE)

# scrape preseason odds
seasons <- 1985:max(seasons)
odds <- scrape_yearly_tables("https://www.basketball-reference.com/leagues/NBA_", seasons, 1, "_preseason_odds.html")
names(odds) <- colnames_preseason_odds
odds_df <- odds %>%
  mutate(champ_odds = as.integer(champ_odds)) %>%
  select(team, year, champ_odds, o_u) %>%
  rename_teams()

write.csv(odds_df, "data/preseason_odds_1980-2023.csv", row.names = FALSE)

# merge with team stats
all_team_stats <- all_team_stats %>%
  merge(odds_df, by = c("team", "year"), all = TRUE)

# scrape playoff team stat tables: total, opp total, per 100 poss, opp per 100 poss, advanced, shooting, opp shooting 
team_stats_playoffs <- scrape_team_stats(seasons, regular_season = FALSE)
keep_name_cols <- c("team", "year")
cols_to_rename <- setdiff(names(team_stats_playoffs), keep_name_cols)
new_colnames <- paste0("p_", cols_to_rename)
names(team_stats_playoffs) <- c(keep_name_cols, new_colnames)
  
write.csv(team_stats_playoffs, "data/team_stats_playoffs_1980-2023.csv", row.names = FALSE) 

breakdown = read.csv("data/team_breakdown.csv")

all_team_stats <- all_team_stats %>%
  merge(team_stats_playoffs, by = c("team", "year"), all = TRUE) %>%
  merge(coaches_df, by.x = c("team", "year", "start_coach"), by.y = c("team", "year", "coach_id"), all.x = TRUE) %>%
  merge(coaches_df, by.x = c("team", "year", "end_coach"), by.y = c("team", "year", "coach_id"), all.x = TRUE, suffixes = c("_start", "_end")) %>%
  merge(breakdown, by = "year") %>%
  select(team, year, playoffs, everything()) %>%
  select(-c(coach_start, coach_end)) %>%
  arrange(team, year)


write.csv(team_stats_playoffs, "data/all_team_stats_1980-2023.csv", row.names = FALSE)

na_counts <- colSums(is.na(df))
nas <- na_counts[na_counts != 0]

#new <- scrape_bballref("https://www.basketball-reference.com/playoffs/NBA_2005.html", 10)
#new2 <- data.frame(new)
