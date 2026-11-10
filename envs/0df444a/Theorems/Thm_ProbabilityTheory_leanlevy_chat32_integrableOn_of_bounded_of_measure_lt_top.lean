-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
-- name    : ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:52:01.645201+00:00
-- url     : https://prove2.me/theorems/3b5a5961-cd65-4f89-b7cd-4d308f940312
-- title:
--   Bounded continuous functions are integrable on finite measure sets
-- statement:
--   A continuous uniformly bounded function is integrable where the measure is finite.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3676-L3683

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top {s : Set ℝ} {μ : Measure ℝ}
    (hs : μ s < ⊤) {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_cont : Continuous f) {M : ℝ} (hf_bnd : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn f s μ := by sorry
