-- Prove2me | Theorems.Thm_TrimmedWorkTape_normalize_step
-- name    : TrimmedWorkTape.normalize_step
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:12:58.002706+00:00
-- url     : https://prove2.me/theorems/e607d408-452d-5d51-820a-a0a93935adbd
-- title:
--   Work-tape normalization preserves the native transition and its emitted symbol
-- statement:
--   For any native deterministic transition table, input and starting configuration, normalize the next configuration by discarding absolute work-head coordinates and trailing blank cells. The normalized next configuration and emitted output symbol are the same whether the starting configuration was normalized before taking the step.
-- source:
--   Universal multitape machine and work-tape zipper in the Prove2Me Complexitylib definition library.

import Definitions.Def_TrimmedNativeWorkTape

open Turing.MultiTapeTM.Universal TrimmedWorkTape

theorem TrimmedWorkTape.normalize_step (d : Desc) (x : List ℕ) (c : SCfg) :
    Prod.map normalizeConfiguration id (step d x (normalizeConfiguration c)) =
      Prod.map normalizeConfiguration id (step d x c) := by sorry
