-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal
-- name    : ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:50:29.43701+00:00
-- url     : https://prove2.me/theorems/effb98ab-6a56-4edb-9aef-e524533168a0
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal
-- statement:
--   Every marginal `μ.map (X t)` of a Lévy process is infinitely divisible. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L197

import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction

universe u_2 u_3
theorem ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal : ∀ {Ω : Type u_2} [inst : MeasurableSpace Ω] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
  [@InnerProductSpace Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)]
  [inst_3 : MeasurableSpace E]
  [@BorelSpace E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      inst_3]
  [@SecondCountableTopology E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))]
  [@MeasurableAdd₂ E inst_3
      (@AddCommMagma.toAdd E
        (@AddCommSemigroup.toAddCommMagma E
          (@AddCommMonoid.toAddCommSemigroup E
            (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)))))]
  {X : NNReal → Ω → E} {μ : @MeasureTheory.Measure Ω inst} [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsLevyProcess Ω E inst inst_3
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1)) X μ →
    (∀ (t : NNReal), @Measurable Ω E inst inst_3 (X t)) →
      ∀ (t : NNReal),
        @ProbabilityTheory.IsInfinitelyDivisible E
          (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)) inst_3
          (@MeasureTheory.Measure.map Ω E inst inst_3 (X t) μ) := by sorry
