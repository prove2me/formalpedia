-- Prove2me | Theorems.Thm_ProbabilityTheory_IsPoissonProcess_hasStationaryIncrements
-- name    : ProbabilityTheory.IsPoissonProcess.hasStationaryIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:12:03.154158+00:00
-- url     : https://prove2.me/theorems/9db41303-f41e-4983-87e5-d444fc97bfe3
-- title:
--   LeanLevy: ProbabilityTheory.IsPoissonProcess.hasStationaryIncrements
-- statement:
--   The ℤ-valued increments of a Poisson process are stationary. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/target_compat/LeanLevy/Processes/PoissonProcess.lean#L75

import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Probability_Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_Kolmogorov

universe u_1
theorem ProbabilityTheory.IsPoissonProcess.hasStationaryIncrements : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {N : NNReal → Ω → Nat} {rate : NNReal} {μ : @MeasureTheory.Measure Ω inst},
  @ProbabilityTheory.IsPoissonProcess Ω inst N rate μ →
    @ProbabilityTheory.HasStationaryIncrements NNReal Ω Int
      (@AddMonoidWithOne.toAddMonoid NNReal
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNReal
          (@NonAssocSemiring.toAddCommMonoidWithOne NNReal (@Semiring.toNonAssocSemiring NNReal NNReal.instSemiring))))
      inst Int.instMeasurableSpace Int.instSub (fun t ω => @Nat.cast Int instNatCastInt (N t ω)) μ := by sorry
