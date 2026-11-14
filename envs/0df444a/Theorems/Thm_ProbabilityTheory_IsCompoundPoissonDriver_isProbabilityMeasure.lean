-- Prove2me | Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_isProbabilityMeasure
-- name    : ProbabilityTheory.IsCompoundPoissonDriver.isProbabilityMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:41:17.24098+00:00
-- url     : https://prove2.me/theorems/b4bb2836-2f59-4149-ab12-1c84d473464e
-- title:
--   LeanLevy: ProbabilityTheory.IsCompoundPoissonDriver.isProbabilityMeasure
-- statement:
--   A compound Poisson driver lives on a probability space. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L115

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli

universe u_1
theorem ProbabilityTheory.IsCompoundPoissonDriver.isProbabilityMeasure : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {τ Y : Nat → Ω → Real} {r : NNReal}
  {ν' : @MeasureTheory.Measure Real Real.measurableSpace} {μ : @MeasureTheory.Measure Ω inst},
  @ProbabilityTheory.IsCompoundPoissonDriver Ω inst τ Y r ν' μ → @MeasureTheory.IsProbabilityMeasure Ω inst μ := by sorry
