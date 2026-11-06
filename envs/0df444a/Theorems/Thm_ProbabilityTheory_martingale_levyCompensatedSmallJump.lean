-- Prove2me | Theorems.Thm_ProbabilityTheory_martingale_levyCompensatedSmallJump
-- name    : ProbabilityTheory.martingale_levyCompensatedSmallJump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:51:16.831545+00:00
-- url     : https://prove2.me/theorems/a4ed8dd7-1a90-4845-886f-769316d97d3c
-- title:
--   LeanLevy: ProbabilityTheory.martingale_levyCompensatedSmallJump
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonMartingale.lean#L545

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem ProbabilityTheory.martingale_levyCompensatedSmallJump [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    MeasureTheory.Martingale (levyCompensatedSmallJumpVersion hd hν)
      (prmFiltration K X ν hd.measurable_count hd.measurable_point) μ := by sorry
