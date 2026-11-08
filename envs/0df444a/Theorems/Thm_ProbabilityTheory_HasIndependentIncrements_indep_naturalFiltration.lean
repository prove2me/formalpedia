-- Prove2me | Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indep_naturalFiltration
-- name    : ProbabilityTheory.HasIndependentIncrements.indep_naturalFiltration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:24:40.277636+00:00
-- url     : https://prove2.me/theorems/d809a0fd-389e-47e9-a61e-80818f16c1f5
-- title:
--   LeanLevy: ProbabilityTheory.HasIndependentIncrements.indep_naturalFiltration
-- statement:
--   For a process with independent increments starting at zero, the increment The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/StochasticProcess.lean#L398

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
universe u_1 u_2 u_3

theorem ProbabilityTheory.HasIndependentIncrements.indep_naturalFiltration :
  ∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : LinearOrder ι] [inst_1 : MeasurableSpace Ω]
  [inst_2 : MeasurableSpace E] [inst_3 : AddGroup E] [inst_4 : Zero ι] [inst_5 : TopologicalSpace E]
  [inst_6 : TopologicalSpace.MetrizableSpace E] [inst_7 : BorelSpace E] [MeasurableSub₂ E] {X : ι → Ω → E}
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsZeroOrProbabilityMeasure μ],
  ProbabilityTheory.HasIndependentIncrements X μ →
    ∀ (hX : ∀ (i : ι), MeasureTheory.StronglyMeasurable (X i)),
      (X 0 = fun x => 0) →
        (∀ (i : ι), 0 ≤ i) →
          ∀ {s t : ι},
            s ≤ t →
              ProbabilityTheory.Indep (MeasurableSpace.comap (ProbabilityTheory.increment X s t) inst_2)
                ((MeasureTheory.Filtration.natural (fun i => X i) hX).seq s) μ := by sorry
