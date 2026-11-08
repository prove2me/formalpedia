-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_nat_mul
-- name    : ProbabilityTheory.leanlevy_chat22_charFun_nat_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:27:55.024442+00:00
-- url     : https://prove2.me/theorems/82da4123-a970-468d-a12f-436a451a8ef8
-- title:
--   Lévy characteristic-function natural-time power law
-- statement:
--   The time-ns marginal characteristic function of a Lévy process is the nth power of its time-s characteristic function.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean lk_charFun_nat_mul lines 234–242; the zero-time helper is inlined in the candidate.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_marginal_mul
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_charFun_nat_mul
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (n : ℕ) (s : ℝ≥0) (ξ : E) :
    charFun (μ.map (X ((n : ℝ≥0) * s))) ξ = (charFun (μ.map (X s)) ξ) ^ n := by sorry
