-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_marksSum_eq
-- name    : ProbabilityTheory.integral_marksSum_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:27:57.703214+00:00
-- url     : https://prove2.me/theorems/41a54ac8-a77d-4a61-ac7d-475118a2a9d1
-- title:
--   First moment of a finite sum of Poisson partition marks
-- statement:
--   The expectation of a sum of j integrable Poisson partition marks equals j times the mark-law expectation, matching the original LeanLevy first-moment lemma.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/RandomMeasure/PoissonPointFamily.lean private integral_marksSum_eq, lines 469–487.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.integral_marksSum_eq
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ =
      (j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k) := by sorry
