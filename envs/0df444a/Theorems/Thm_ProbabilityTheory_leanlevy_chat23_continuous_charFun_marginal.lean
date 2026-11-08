-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat23_continuous_charFun_marginal
-- name    : ProbabilityTheory.leanlevy_chat23_continuous_charFun_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:45:56.842103+00:00
-- url     : https://prove2.me/theorems/48ddebff-a767-4d73-baf1-14235c6ae2c5
-- title:
--   Continuity of the marginal characteristic function of a Levy process
-- statement:
--   At a fixed frequency, the characteristic function of the one-time distribution of a Levy process varies continuously with nonnegative time.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; Levy/CharacteristicExponent.lean continuity corollary, deduced from the accepted original IsLevyProcess.charFun_eq_exp_mul theorem.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat23_continuous_charFun_marginal
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by sorry
