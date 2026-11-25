-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_log_normSq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.leviV_log_normSq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:41.844032+00:00
-- url     : https://prove2.me/theorems/cb87f54c-9857-430e-b83e-bb927d5abc4a
-- title:
--   Y: levi V log norm Sq
-- statement:
--   The Y construction uses the levi V log norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L107-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L107-L123

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.leviV_log_normSq {n : ℕ} {G : V n → ℂ} {x : V n} (hG : ContDiffAt ℂ 2 G x)
    (h0 : G x ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((Real.log (Complex.normSq (G v)) : ℝ) : ℂ)) x ξ = 0 := by sorry
