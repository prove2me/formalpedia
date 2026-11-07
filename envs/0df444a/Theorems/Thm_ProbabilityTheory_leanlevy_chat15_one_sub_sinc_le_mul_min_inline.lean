-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_one_sub_sinc_le_mul_min_inline
-- name    : ProbabilityTheory.leanlevy_chat15_one_sub_sinc_le_mul_min_inline
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:20:01.519015+00:00
-- url     : https://prove2.me/theorems/158f3107-d413-423a-859b-46c78476d2d5
-- title:
--   Standalone source upper sinc bound
-- statement:
--   The upper two-sided sinc estimate follows by complex exponential cubic Taylor control on |x|≤1 and an elementary large-argument bound.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 1529-1553 and 1556-1583; inlining source-exact private complex Taylor and cubic sine lemmas avoids dependence on a still Open imported helper.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_one_sub_sinc_le_mul_min_inline :
  ∀ (x : ℝ), 1 - Real.sinc x ≤ 2 * min 1 (x ^ 2) := by sorry
