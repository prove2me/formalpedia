-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedBudget_node_budget
-- name    : ThreeSum.LightTernaryWantedBudget.node_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:42.606206+00:00
-- url     : https://prove2.me/theorems/ef18a0cd-83d5-467c-9d64-0b2b4c2045c3
-- title:
--   Light Ternary Wanted Budget: node budget
-- statement:
--   Arithmetic cost depends on the bit length of the signed target.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBudget.lean#L6-L13
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBudget.lean#L6-L13

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBudget
open LightTernaryWantedCanonical

theorem ThreeSum.LightTernaryWantedBudget.node_budget (P V W : ℕ) (hV : V ≤ 2^W) :
    overhead P V+stepCost V+40 ≤ 1000*(P+W+3) := by sorry
