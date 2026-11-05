-- Prove2me | Theorems.Thm_ProbabilityTheory_map_poissonTimeCount
-- name    : ProbabilityTheory.map_poissonTimeCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:53:43.656039+00:00
-- url     : https://prove2.me/theorems/0b1b6459-769b-4b76-93a3-500aedb9b0cf
-- title:
--   LeanLevy: ProbabilityTheory.map_poissonTimeCount
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L124

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω} {A : Set E} {s t : ℝ}

theorem ProbabilityTheory.map_poissonTimeCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) (ht : 0 ≤ t) :
    μ.map (poissonTimeCount K X A t)
      = (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by sorry
