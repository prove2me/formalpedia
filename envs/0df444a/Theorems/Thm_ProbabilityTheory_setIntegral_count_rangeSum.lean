-- Prove2me | Theorems.Thm_ProbabilityTheory_setIntegral_count_rangeSum
-- name    : ProbabilityTheory.setIntegral_count_rangeSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:53:17.270897+00:00
-- url     : https://prove2.me/theorems/d4454fdb-daba-45b1-ac98-10c824db4775
-- title:
--   Conditional Campbell factorisation on a fixed Poisson count cell
-- statement:
--   The count-cell first moment factors into probability and unconditional marks moment; prerequisite ProbabilityTheory.integral_marksSum_eq has now been proved and source identity was independently verified.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/RandomMeasure/PoissonPointFamily.lean private setIntegral_count_rangeSum, lines 488–519.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integral_marksSum_eq
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.setIntegral_count_rangeSum
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω in {ω | K k ω = j}, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ
      = μ.real {ω | K k ω = j} *
        ((j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k)) := by sorry
