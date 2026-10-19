-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenWordMultiplicationBad_density_tendsto_zero
-- name    : SoficGroups.KunActualSoficRootRadius.chosenWordMultiplicationBad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/458a8d7e-4799-40d8-bf63-dd91cf6d1467
-- title:
--   SoficGroups.KunActualSoficRootRadius.chosenWordMultiplicationBad_density_tendsto_zero
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

theorem SoficGroups.KunActualSoficRootRadius.chosenWordMultiplicationBad_density_tendsto_zero
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (g h : G) :
    Tendsto
      (fun n =>
        ((chosenWordMultiplicationBad A s w n g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by sorry
