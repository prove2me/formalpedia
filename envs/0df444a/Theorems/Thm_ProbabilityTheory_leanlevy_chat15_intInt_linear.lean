-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_intInt_linear
-- name    : ProbabilityTheory.leanlevy_chat15_intInt_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:12:11.315476+00:00
-- url     : https://prove2.me/theorems/ddd8cd21-06a1-4de7-9ac5-6ad667133cc1
-- title:
--   Symmetric linear interval integral
-- statement:
--   The first moment of the translated symmetric unit interval equals twice the translation.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 142–145, source-exact private lemma.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_intInt_linear (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by sorry
