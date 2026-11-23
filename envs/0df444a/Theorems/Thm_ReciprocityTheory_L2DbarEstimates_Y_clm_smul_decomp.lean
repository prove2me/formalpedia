-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_clm_smul_decomp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.clm_smul_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:02.531809+00:00
-- url     : https://prove2.me/theorems/f6016c08-6f72-437b-8936-66f9432d87cd
-- title:
--   Y: clm smul decomp
-- statement:
--   The Y construction uses the clm smul decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L16-L20

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

theorem ReciprocityTheory.L2DbarEstimates.Y.clm_smul_decomp {n : ℕ} (D : V n →L[ℝ] ℂ) (c : ℂ) (e : V n) :
    D (c • e) = c.re * D e + c.im * D (I • e) := by sorry
