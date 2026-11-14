-- Prove2me | Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
-- name    : ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:15:41.284428+00:00
-- url     : https://prove2.me/theorems/fa9156ce-f7ff-4366-845c-3e09c8633d1c
-- title:
--   LeanLevy: ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L130

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, ∀ n, 0 < τ n ω := by sorry
