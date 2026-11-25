-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_norm_sum_mul_sq_le
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.norm_sum_mul_sq_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:54.173802+00:00
-- url     : https://prove2.me/theorems/92017a08-3763-48f6-9b3e-86bdcc2e27ee
-- title:
--   Levi Form Quadratic Sums: norm sum mul sq le
-- statement:
--   The Levi Form Quadratic Sums construction uses the norm sum mul sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean#L23-L30

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.norm_sum_mul_sq_le {d : ℕ} (x y : Fin d → ℂ) :
    ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ ^ 2) * (∑ k, ‖y k‖ ^ 2) := by sorry
