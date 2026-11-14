-- Prove2me | Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
-- name    : ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:26:00.649531+00:00
-- url     : https://prove2.me/theorems/4f9baf5d-e2b6-4c28-b9f4-7dd5badaaa79
-- title:
--   LeanLevy: ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival
-- statement:
--   The arrival times of a compound Poisson driver almost surely tend to `+∞`. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L193

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
universe u_1

theorem ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival :
  ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : NNReal} {ν' : MeasureTheory.Measure ℝ}
  {μ : MeasureTheory.Measure Ω},
  ProbabilityTheory.IsCompoundPoissonDriver τ Y r ν' μ →
    0 < r → ∀ᵐ (ω : Ω) ∂μ, Filter.Tendsto (fun n => ProbabilityTheory.arrival τ n ω) Filter.atTop Filter.atTop := by sorry
