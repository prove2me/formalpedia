-- Prove2me | Theorems.Thm_ProbabilityTheory_setIntegral_count_marksFun
-- name    : ProbabilityTheory.setIntegral_count_marksFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:58:12.386307+00:00
-- url     : https://prove2.me/theorems/a6b19315-0a42-49be-8121-7742b7771678
-- title:
--   Count-cell factorisation for a measurable mark functional
-- statement:
--   For a Poisson point family, the count on one piece is independent of its mark sequence, so conditioning on an exact count factors the integral of every measurable real-valued marks functional.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean lines 606–632; private setIntegral_count_marksFun.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ProbabilityTheory.setIntegral_count_marksFun
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ)
    {ψ : (ℕ → E) → ℝ} (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ =
      μ.real {ω | K k ω = j} * ∫ ω, ψ (fun n => X k n ω) ∂μ := by sorry
