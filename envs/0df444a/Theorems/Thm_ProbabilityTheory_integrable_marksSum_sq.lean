-- Prove2me | Theorems.Thm_ProbabilityTheory_integrable_marksSum_sq
-- name    : ProbabilityTheory.integrable_marksSum_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:58:14.980276+00:00
-- url     : https://prove2.me/theorems/8dd0461e-5dbd-4a40-8da7-2ce1b840bcc8
-- title:
--   Integrability of a finite Poisson marks sum squared
-- statement:
--   A finite sum of independent Poisson marks has an integrable square when both a mark and its square are integrable against the intensity restricted to the corresponding partition piece.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean lines 634–662; private integrable_marksSum_sq.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ProbabilityTheory.integrable_marksSum_sq
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k)))
    (j : ℕ) :
    Integrable (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) μ := by sorry
