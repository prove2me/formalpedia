-- Prove2me | Theorems.Thm_ProbabilityTheory_setIntegral_sq_pieceSum_eq
-- name    : ProbabilityTheory.setIntegral_sq_pieceSum_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:30:53.246391+00:00
-- url     : https://prove2.me/theorems/d0878f26-5aa0-43ce-bcfc-b74b279a2d2f
-- title:
--   Conditioned squared Poisson piece-sum identity
-- statement:
--   The squared Poisson piece-sum integral on the event of exactly j points equals the Poisson probability times the fixed-j second moment of the marks.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean lines 734–759, private setIntegral_sq_pieceSum_eq.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_setIntegral_count_marksFun
import Theorems.Thm_ProbabilityTheory_integral_marksSum_sq_eq
import Theorems.Thm_ProbabilityTheory_measureReal_count_eq
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ProbabilityTheory.setIntegral_sq_pieceSum_eq
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ}
    (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k)))
    (j : ℕ) :
    ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ =
      (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} *
      ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) +
       (j : ℝ) * ((j : ℝ) - 1) *
       (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by sorry
