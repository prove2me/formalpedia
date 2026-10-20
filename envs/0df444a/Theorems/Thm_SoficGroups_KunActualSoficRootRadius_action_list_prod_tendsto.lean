-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_action_list_prod_tendsto
-- name    : SoficGroups.KunActualSoficRootRadius.action_list_prod_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/c510aed8-bf4c-4699-97f8-8a7b9f76d6b4
-- title:
--   SoficGroups.KunActualSoficRootRadius.action_list_prod_tendsto
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualSoficRootRadius.action_list_prod_tendsto
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (l : List G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          ((A.model n).action l.prod)
          ((l.map (A.model n).action).prod))
      atTop (𝓝 0) := by sorry
