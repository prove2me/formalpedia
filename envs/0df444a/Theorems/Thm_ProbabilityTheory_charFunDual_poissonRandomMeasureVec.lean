-- Prove2me | Theorems.Thm_ProbabilityTheory_charFunDual_poissonRandomMeasureVec
-- name    : ProbabilityTheory.charFunDual_poissonRandomMeasureVec
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:07:17.934373+00:00
-- url     : https://prove2.me/theorems/6178da17-4874-4326-8003-2f98ea387f78
-- title:
--   LeanLevy Poisson superposition helper: charFunDual_poissonRandomMeasureVec
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

theorem ProbabilityTheory.charFunDual_poissonRandomMeasureVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L
      = ∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by sorry
