-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_intInt_quadratic
-- name    : ProbabilityTheory.leanlevy_chat15_intInt_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:01:26.131487+00:00
-- url     : https://prove2.me/theorems/e7b7df6f-26e2-4cab-a3ee-229fd836fad4
-- title:
--   Symmetric quadratic interval integral
-- statement:
--   The integral of (xi + u)^2 over the symmetric unit interval is 2 xi^2 + 2/3.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 147–150, private lemma promotion.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_intInt_quadratic
    (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by sorry
