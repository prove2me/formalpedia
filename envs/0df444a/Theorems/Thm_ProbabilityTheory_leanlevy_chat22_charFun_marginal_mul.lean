-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_marginal_mul
-- name    : ProbabilityTheory.leanlevy_chat22_charFun_marginal_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:36:34.575201+00:00
-- url     : https://prove2.me/theorems/400ddb48-60ae-42ea-a541-e4cafd189605
-- title:
--   Multiplicativity of Lévy marginal characteristic functions
-- statement:
--   The characteristic function of a Lévy process at time s+k equals the product of its marginal characteristic functions at times s and k.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean private lk_charFun_mul lines 108–125; Processes/StochasticProcess.lean HasIndependentIncrements.indepFun_increment lines 107–122. Dependencies inlined.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_charFun_marginal_mul
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (s k : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + k))) ξ = charFun (μ.map (X s)) ξ * charFun (μ.map (X k)) ξ := by sorry
