-- Prove2me | Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indepFun_increment
-- name    : ProbabilityTheory.HasIndependentIncrements.indepFun_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:07:34.935818+00:00
-- url     : https://prove2.me/theorems/5f33be53-d75e-4e15-a03b-2ce5691d8c5c
-- title:
--   LeanLevy: ProbabilityTheory.HasIndependentIncrements.indepFun_increment
-- statement:
--   A process with independent increments has independent increments over two adjacent non-overlapping intervals. Pinned source theorem, with its original proof previously compiled; awaiting remote Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/StochasticProcess.lean#L107

import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

universe u_1 u_2 u_3
theorem ProbabilityTheory.HasIndependentIncrements.indepFun_increment : ∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : Preorder ι] [inst_1 : MeasurableSpace Ω]
  [inst_2 : MeasurableSpace E] [inst_3 : Sub E] {X : ι → Ω → E} {μ : @MeasureTheory.Measure Ω inst_1},
  @ProbabilityTheory.HasIndependentIncrements ι Ω E inst inst_1 inst_2 inst_3 X μ →
    ∀ {s t u : ι},
      @LE.le ι (@Preorder.toLE ι inst) s t →
        @LE.le ι (@Preorder.toLE ι inst) t u →
          @ProbabilityTheory.IndepFun Ω E E inst_1 inst_2 inst_2 (@ProbabilityTheory.increment ι Ω E inst_3 X s t)
            (@ProbabilityTheory.increment ι Ω E inst_3 X t u) μ := by sorry
