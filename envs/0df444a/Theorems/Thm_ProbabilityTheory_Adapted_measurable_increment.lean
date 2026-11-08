-- Prove2me | Theorems.Thm_ProbabilityTheory_Adapted_measurable_increment
-- name    : ProbabilityTheory.Adapted.measurable_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:04:53.341117+00:00
-- url     : https://prove2.me/theorems/a3485ea3-1508-4f6c-9433-ed619238e841
-- title:
--   LeanLevy: ProbabilityTheory.Adapted.measurable_increment
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The original mathematical assertion is retained with explicit names and source-compatible universe declarations. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/StochasticProcess.lean#L442

import Definitions.Def_LeanLevy_Processes_StochasticProcess

open MeasureTheory ProbabilityTheory

universe u v w
variable {ι : Type u} {Ω : Type v} {E : Type w} {m : MeasurableSpace Ω} [Preorder ι] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E] [Sub E] [MeasurableSub₂ E]

theorem ProbabilityTheory.Adapted.measurable_increment
    {𝓕 : Filtration ι m} {X : ι → Ω → E}
    (hX : Adapted 𝓕 (fun i => X i))
    {s t : ι} (hst : s ≤ t) :
    Measurable[𝓕 t] (increment X s t) := by sorry
