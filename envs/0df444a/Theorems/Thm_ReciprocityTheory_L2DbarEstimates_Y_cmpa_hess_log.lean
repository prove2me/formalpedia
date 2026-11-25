-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_hess_log
-- name    : ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:12.041031+00:00
-- url     : https://prove2.me/theorems/5580bb0f-d563-5b8d-868e-c716532db2fe
-- title:
--   Y: cmpa hess log
-- statement:
--   The Y construction uses the cmpa hess log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaCHessComp.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaCHessComp.lean#L76-L92

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
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

theorem ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log {g : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U) (hxU : x ∈ U)
    (hg : DifferentiableOn ℂ g U) (hne : ∀ v ∈ U, g v ≠ 0) (j k : Fin n) :
    wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x = 0 := by sorry
