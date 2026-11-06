-- Prove2me | Theorems.Thm_ProbabilityTheory_aestronglyMeasurable_levyCompensatedSmallJump_band
-- name    : ProbabilityTheory.aestronglyMeasurable_levyCompensatedSmallJump_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:18:21.898224+00:00
-- url     : https://prove2.me/theorems/7aca2850-ffc7-4ac8-bc14-c90fcde7e31e
-- title:
--   LeanLevy source: compensated small-jump band sigma measurability
-- statement:
--   The L2 compensated small-jump integral over a time band is almost everywhere strongly measurable in the Poisson evaluation sigma-algebra of that band.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}

theorem ProbabilityTheory.aestronglyMeasurable_levyCompensatedSmallJump_band [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (s t : ℝ) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Ioc s t ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp _)) μ := by sorry
