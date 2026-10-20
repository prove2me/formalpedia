-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_action_list_prod_tendsto
-- name    : SoficGroups.SourceGeneratedWordCrossing.action_list_prod_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/7f7bff6c-c98e-49b3-8a46-38a8f399ecd9
-- title:
--   SoficGroups.SourceGeneratedWordCrossing.action_list_prod_tendsto
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceGeneratedWordCrossing.action_list_prod_tendsto
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (l : List G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          ((A.model n).action l.prod)
          ((l.map (A.model n).action).prod))
      atTop (nhds 0) := by sorry
