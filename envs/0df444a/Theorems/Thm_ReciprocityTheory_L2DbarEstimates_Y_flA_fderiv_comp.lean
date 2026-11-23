-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_fderiv_comp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flA_fderiv_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:37.546207+00:00
-- url     : https://prove2.me/theorems/4c8a7d84-7c03-4aae-ac3a-0fe9b90a1220
-- title:
--   Y: fl A fderiv comp
-- statement:
--   The Y construction uses the fl A fderiv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L38-L41

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

theorem ReciprocityTheory.L2DbarEstimates.Y.flA_fderiv_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (v : V n) :
    fderiv ℝ (U ∘ G) y v = fderiv ℝ U (G y) (fderiv ℂ G y v) := by sorry
