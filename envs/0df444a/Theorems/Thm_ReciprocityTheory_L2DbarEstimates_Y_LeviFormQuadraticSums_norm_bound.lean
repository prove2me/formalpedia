-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_norm_bound
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.norm_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:20.251098+00:00
-- url     : https://prove2.me/theorems/6b774c59-29bd-483d-b94c-ab322eb6517c
-- title:
--   Levi Form Quadratic Sums: norm bound
-- statement:
--   The Levi Form Quadratic Sums construction uses the norm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeD.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeD.lean#L16-L29

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n d : ℕ} {p : V n → V d} {U : Set (V n)}

theorem ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.norm_bound (c : ℝ) (hc : 0 < c) (x y : Fin d → ℂ) (P : V d) (hP : ∀ k, ‖x k‖ = ‖P k‖)
    (B : ℝ) (hB : B = ∑ k, ‖y k‖ ^ 2) :
    ‖∑ k, (c : ℂ)⁻¹ * (x k * y k)‖ ^ 2 ≤ (‖P‖ ^ 2 / c) * (c⁻¹ * B) := by sorry
