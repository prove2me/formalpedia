-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_eq_dv
-- name    : ReciprocityTheory.L2DbarEstimates.Y.leviV_eq_dv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:53.465809+00:00
-- url     : https://prove2.me/theorems/49e5f5dd-8a43-42b0-bde2-7a68fe2f11d9
-- title:
--   Y: levi V eq dv
-- statement:
--   The Y construction uses the levi V eq dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L66-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L66-L99

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

theorem ReciprocityTheory.L2DbarEstimates.Y.leviV_eq_dv {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (ξ : Fin n → ℂ) :
    leviV n g y ξ =
      dv (fderiv ℝ (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) y) (WithLp.toLp 2 ξ) := by sorry
