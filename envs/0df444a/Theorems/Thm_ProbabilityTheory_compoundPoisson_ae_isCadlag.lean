-- Prove2me | Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
-- name    : ProbabilityTheory.compoundPoisson_ae_isCadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:16:32.309049+00:00
-- url     : https://prove2.me/theorems/74d4b2ab-93f9-48be-8d72-8b726fd40c72
-- title:
--   LeanLevy: ProbabilityTheory.compoundPoisson_ae_isCadlag
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L339

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.compoundPoisson_ae_isCadlag {Ω : Type*} [MeasurableSpace Ω] {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t => compoundPoisson b τ Y t ω) := by sorry
