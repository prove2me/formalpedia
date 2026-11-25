-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_apply_sum
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flA_apply_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:45.696262+00:00
-- url     : https://prove2.me/theorems/77ad1863-df3d-4108-a357-3a918b46b6ad
-- title:
--   Y: fl A apply sum
-- statement:
--   The Y construction uses the fl A apply sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L19-L22

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.flA_apply_sum (D : V n →L[ℂ] V n) (ξ : Fin n → ℂ) (a : Fin n) :
    D (WithLp.toLp 2 ξ) a = ∑ j, ξ j * D (bas n j) a := by sorry
