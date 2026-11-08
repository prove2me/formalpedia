-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_rat_pow
-- name    : ProbabilityTheory.leanlevy_chat22_charFun_rat_pow
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:35:56.83476+00:00
-- url     : https://prove2.me/theorems/c0ef9a01-214c-4cff-aa18-f6930c8122eb
-- title:
--   Lévy characteristic-function rational-time power law
-- statement:
--   The Lévy characteristic function at k/n is the kth power of the characteristic function at 1/n.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean lk_charFun_rat_pow lines 127–138; proof is a direct instance of source-exact natural powers.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_nat_mul
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_charFun_rat_pow
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (k n : ℕ) (ξ : E) :
    charFun (μ.map (X ((k : ℝ≥0) / (n : ℝ≥0)))) ξ =
      (charFun (μ.map (X (1 / (n : ℝ≥0)))) ξ) ^ k := by sorry
