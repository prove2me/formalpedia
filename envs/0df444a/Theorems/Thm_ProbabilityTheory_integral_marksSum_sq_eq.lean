-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_marksSum_sq_eq
-- name    : ProbabilityTheory.integral_marksSum_sq_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:00:44.144846+00:00
-- url     : https://prove2.me/theorems/2a0d5868-81a5-4d89-9a8f-9563bdc683bc
-- title:
--   Second moment of a fixed finite independent mark sum
-- statement:
--   E[(sum of j independent marks)^2] equals j times the mark second moment plus j(j-1) times the square of the mark mean; the exact LeanLevy proof separates diagonal and off-diagonal terms.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean lines 664–732, private integral_marksSum_sq_eq.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ProbabilityTheory.integral_marksSum_sq_eq
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ}
    (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k)))
    (j : ℕ) :
    ∫ ω, (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2 ∂μ =
      (j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) +
      (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2 := by sorry
