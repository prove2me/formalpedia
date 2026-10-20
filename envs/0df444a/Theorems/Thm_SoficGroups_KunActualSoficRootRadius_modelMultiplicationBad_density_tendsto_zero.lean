-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_modelMultiplicationBad_density_tendsto_zero
-- name    : SoficGroups.KunActualSoficRootRadius.modelMultiplicationBad_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/4a50c7dc-f2fa-4a4f-882e-cf2b128032d5
-- title:
--   SoficGroups.KunActualSoficRootRadius.modelMultiplicationBad_density_tendsto_zero
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

theorem SoficGroups.KunActualSoficRootRadius.modelMultiplicationBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (g h : G) :
    Tendsto
      (fun n =>
        ((modelMultiplicationBad (A.model n) g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by sorry
