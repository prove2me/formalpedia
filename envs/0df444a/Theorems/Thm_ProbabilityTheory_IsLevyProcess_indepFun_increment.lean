-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
-- name    : ProbabilityTheory.IsLevyProcess.indepFun_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:47:55.648844+00:00
-- url     : https://prove2.me/theorems/32e00b9b-07d5-43a6-aa1c-594931ea0d22
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.indepFun_increment
-- statement:
--   Two non-overlapping increments of a Lévy process are pairwise independent. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/LevyProcess.lean#L67

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log

universe u_1 u_2
theorem ProbabilityTheory.IsLevyProcess.indepFun_increment : ∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace Ω] [inst_1 : MeasurableSpace E] [inst_2 : TopologicalSpace E]
  [inst_3 : AddGroup E] {X : NNReal → Ω → E} {μ : @MeasureTheory.Measure Ω inst},
  @ProbabilityTheory.IsLevyProcess Ω E inst inst_1 inst_2 inst_3 X μ →
    ∀ {s t u : NNReal},
      @LE.le NNReal (@Preorder.toLE NNReal (@PartialOrder.toPreorder NNReal NNReal.instPartialOrder)) s t →
        @LE.le NNReal (@Preorder.toLE NNReal (@PartialOrder.toPreorder NNReal NNReal.instPartialOrder)) t u →
          @ProbabilityTheory.IndepFun Ω E E inst inst_1 inst_1
            (@ProbabilityTheory.increment NNReal Ω E (@SubNegMonoid.toSub E (@AddGroup.toSubNegMonoid E inst_3)) X s t)
            (@ProbabilityTheory.increment NNReal Ω E (@SubNegMonoid.toSub E (@AddGroup.toSubNegMonoid E inst_3)) X t u)
            μ := by sorry
