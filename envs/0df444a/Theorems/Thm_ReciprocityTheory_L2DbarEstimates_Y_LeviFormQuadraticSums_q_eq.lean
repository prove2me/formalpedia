-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_q_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.q_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:17.281785+00:00
-- url     : https://prove2.me/theorems/8836f51a-6953-51de-a69b-9497d4b51fcb
-- title:
--   Levi Form Quadratic Sums: q eq
-- statement:
--   The Levi Form Quadratic Sums construction uses the q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean#L39-L45

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
variable {d : ℕ} (p : V n → V d) (U : Set (V n)) (c : ℝ)

theorem ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.q_eq : (fun x => ((‖p x‖ ^ 2 / c : ℝ) : ℂ)) =
    fun x => ∑ k, (c : ℂ)⁻¹ * (p x k * conj (p x k : ℂ)) := by sorry
