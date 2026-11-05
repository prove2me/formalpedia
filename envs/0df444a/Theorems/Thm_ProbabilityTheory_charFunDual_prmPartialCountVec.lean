-- Prove2me | Theorems.Thm_ProbabilityTheory_charFunDual_prmPartialCountVec
-- name    : ProbabilityTheory.charFunDual_prmPartialCountVec
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:07:21.49987+00:00
-- url     : https://prove2.me/theorems/6b52d3d4-3bea-4815-a4c2-d2da38aaff4e
-- title:
--   LeanLevy Poisson superposition helper: charFunDual_prmPartialCountVec
-- statement:
--   Source-exact private helper from the original LeanLevy PoissonRandomMeasure module, promoted into an owner-private Prove2Me child to permit bounded verification of the finite-dimensional Poisson random-measure independence argument.

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Complex ProbabilityTheory
open scoped ENNReal NNReal Topology
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E]
  {μ : Measure Ω} {A B : Set E} {ω : Ω}

theorem ProbabilityTheory.charFunDual_prmPartialCountVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A)) (n : ℕ)
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L
      = ∏ i, Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
          * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by sorry
