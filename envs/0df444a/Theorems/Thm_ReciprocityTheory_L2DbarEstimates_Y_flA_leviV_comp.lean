-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_leviV_comp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_comp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:23.984977+00:00
-- url     : https://prove2.me/theorems/3dd3b8db-e527-5dbe-812b-1020b0eb595b
-- title:
--   Y: fl A levi V comp
-- statement:
--   The Y construction uses the fl A levi V comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L83-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L83-L117

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

theorem ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : ContDiffAt ℝ 2 U (G y)) (hG : ContDiffAt ℂ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (U ∘ G) y ξ = leviV n U (G y) (fun b => fderiv ℂ G y (WithLp.toLp 2 ξ) b) := by sorry
