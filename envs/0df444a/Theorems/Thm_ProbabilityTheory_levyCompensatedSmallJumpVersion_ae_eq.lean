-- Prove2me | Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJumpVersion_ae_eq
-- name    : ProbabilityTheory.levyCompensatedSmallJumpVersion_ae_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:50:58.419189+00:00
-- url     : https://prove2.me/theorems/a4572e12-3e68-4c41-ae7d-f7c634bc2baa
-- title:
--   LeanLevy: ProbabilityTheory.levyCompensatedSmallJumpVersion_ae_eq
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonMartingale.lean#L522

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem ProbabilityTheory.levyCompensatedSmallJumpVersion_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (t : ℝ≥0) :
    levyCompensatedSmallJumpVersion hd hν t =ᵐ[μ] levyCompensatedSmallJump hd hν (t : ℝ) := by sorry
