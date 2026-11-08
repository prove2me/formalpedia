-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_ne_zero
-- name    : ProbabilityTheory.IsLevyProcess.charFun_marginal_ne_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:45:58.702108+00:00
-- url     : https://prove2.me/theorems/6ff7be33-43b7-44aa-abf2-8a82de67dc5e
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.charFun_marginal_ne_zero
-- statement:
--   The characteristic function of any marginal is nonvanishing. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/LevyProcess.lean#L252

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log

universe u_1 u_3
theorem ProbabilityTheory.IsLevyProcess.charFun_marginal_ne_zero : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
  [inst_2 : @InnerProductSpace Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)]
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
      ∀ (t : NNReal) (ξ : E),
        @Ne Complex
          (@MeasureTheory.charFun E inst_3
            (@InnerProductSpace.toInner Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)
              inst_2)
            (@MeasureTheory.Measure.map Ω E inst inst_3 (X t) μ) ξ)
          (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero)) := by sorry
