-- Prove2me | Theorems.Thm_SoficGroups_KunRootedUniversalToleranceNumerics_rooted_graph_coefficient_small
-- name    : SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_coefficient_small
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/f5933edf-68c6-4c6e-a91e-c0d82d947604
-- title:
--   SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_coefficient_small
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedUniversalToleranceNumerics

theorem SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_coefficient_small
    {d q : ℝ} (hd : 0 < d) (hq : q < 1) :
    0 < d * (1 - q) ^ 2 / 288 ∧
      216 * (d * (1 - q) ^ 2 / 288) < d * (1 - q) ^ 2 := by sorry
