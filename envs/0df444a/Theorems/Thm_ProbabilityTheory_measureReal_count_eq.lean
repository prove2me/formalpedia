-- Prove2me | Theorems.Thm_ProbabilityTheory_measureReal_count_eq
-- name    : ProbabilityTheory.measureReal_count_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:27:45.69795+00:00
-- url     : https://prove2.me/theorems/d53a00ed-7080-4048-a8ab-d8403b012737
-- title:
--   Poisson point family count-cell probability in real mass
-- statement:
--   The probability of exactly j points in a Poisson partition cell equals the Poisson pmf at its intensity. The source uses universe zero for both sample and mark types.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/RandomMeasure/PoissonPointFamily.lean private measureReal_count_eq, lines 520–529.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.measureReal_count_eq
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ}
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ) :
    μ.real {ω | K k ω = j} =
      (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} := by sorry
