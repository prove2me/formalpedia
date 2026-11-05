-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_natCast_poissonRandomMeasure_apply
-- name    : ProbabilityTheory.iIndepFun_natCast_poissonRandomMeasure_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:07:19.961004+00:00
-- url     : https://prove2.me/theorems/c0437f84-2358-4d7f-adb6-1711fae3f83e
-- title:
--   LeanLevy Poisson superposition helper: iIndepFun_natCast_poissonRandomMeasure_apply
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

theorem ProbabilityTheory.iIndepFun_natCast_poissonRandomMeasure_apply {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => (poissonRandomMeasure K X ω (A i)).toReal) μ := by sorry
