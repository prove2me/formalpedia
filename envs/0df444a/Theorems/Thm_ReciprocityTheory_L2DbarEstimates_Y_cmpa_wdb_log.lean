-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_wdb_log
-- name    : ReciprocityTheory.L2DbarEstimates.Y.cmpa_wdb_log
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:14.403917+00:00
-- url     : https://prove2.me/theorems/416c6fc8-45d8-430c-80f4-51ce9f5489ce
-- title:
--   Y: cmpa wdb log
-- statement:
--   The Y construction uses the cmpa wdb log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaCHessComp.lean#L43-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaCHessComp.lean#L43-L62

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

theorem ReciprocityTheory.L2DbarEstimates.Y.cmpa_wdb_log {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℂ 2 g y) (hy : g y ≠ 0) (k : Fin n) :
    wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) y = conj (fderiv ℂ g y (bas n k) / g y) := by sorry
