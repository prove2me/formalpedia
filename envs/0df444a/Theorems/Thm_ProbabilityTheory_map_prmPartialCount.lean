-- Prove2me | Theorems.Thm_ProbabilityTheory_map_prmPartialCount
-- name    : ProbabilityTheory.map_prmPartialCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:07:17.713208+00:00
-- url     : https://prove2.me/theorems/9f35f7a3-a10a-4e33-950b-23567c49e994
-- title:
--   LeanLevy Poisson superposition helper: map_prmPartialCount
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

theorem ProbabilityTheory.map_prmPartialCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (n : ℕ) :
    μ.map (prmPartialCount K X A n)
      = poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal) := by sorry
