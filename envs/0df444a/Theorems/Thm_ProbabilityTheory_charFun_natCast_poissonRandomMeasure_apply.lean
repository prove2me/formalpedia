-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply
-- name    : ProbabilityTheory.charFun_natCast_poissonRandomMeasure_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:07:18.724343+00:00
-- url     : https://prove2.me/theorems/2e61b3e5-2ad0-4458-9d11-deb5c4b2149b
-- title:
--   LeanLevy Poisson superposition helper: charFun_natCast_poissonRandomMeasure_apply
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

theorem ProbabilityTheory.charFun_natCast_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) (ξ : ℝ) :
    charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ
      = Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)) := by sorry
