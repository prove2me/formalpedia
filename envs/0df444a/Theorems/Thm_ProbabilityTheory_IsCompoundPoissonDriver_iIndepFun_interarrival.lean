-- Prove2me | Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_iIndepFun_interarrival
-- name    : ProbabilityTheory.IsCompoundPoissonDriver.iIndepFun_interarrival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:39:31.649237+00:00
-- url     : https://prove2.me/theorems/ff69ef85-841d-48ba-8a2a-1ffc809df4c1
-- title:
--   LeanLevy: ProbabilityTheory.IsCompoundPoissonDriver.iIndepFun_interarrival
-- statement:
--   The interarrival family of a compound Poisson driver is jointly independent: restrict the Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L120

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli

universe u_1
theorem ProbabilityTheory.IsCompoundPoissonDriver.iIndepFun_interarrival : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {τ Y : Nat → Ω → Real} {r : NNReal}
  {ν' : @MeasureTheory.Measure Real Real.measurableSpace} {μ : @MeasureTheory.Measure Ω inst},
  @ProbabilityTheory.IsCompoundPoissonDriver Ω inst τ Y r ν' μ →
    @ProbabilityTheory.iIndepFun Ω Nat inst (fun x => Real) (fun x => Real.measurableSpace) τ μ := by sorry
