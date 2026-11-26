-- Prove2me | Theorems.Thm_Sendov_finite_range
-- name    : Sendov.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:29:10.523886+00:00
-- url     : https://prove2.me/theorems/b15b2a92-d3e6-40d6-b9b4-2404e5ed14c4
-- title:
--   Sendov: finite range
-- statement:
--   **The finite-range claim.**  The right-hand side of equation `stat` of the blog post is
--   strictly less than `1` on the range of degrees and of `α` left open there, that is, on
--   `5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, subject to the feasibility constraint `c ^ 2 ≤ A`.
--
--   This is the original challenge statement.  It is a special case of `finite_range_le_100`,
--   which covers three more degrees: the finite certification was pushed from `97` to `100` so
--   that it meets the large-degree argument of `Sendov.LargeDegree` with room to spare.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Cover.lean#L168-L171
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Cover.lean#L168-L171

import Definitions.Def_Sendov_FiniteRange_Degree5
import Definitions.Def_Sendov_FiniteRange_Degree7
import Definitions.Def_Sendov_FiniteRange_Degree6_6
import Definitions.Def_Sendov_FiniteRange_Degree8_9
import Definitions.Def_Sendov_FiniteRange_Degree10_11
import Definitions.Def_Sendov_FiniteRange_Degree12_13
import Definitions.Def_Sendov_FiniteRange_Degree14_15
import Definitions.Def_Sendov_FiniteRange_Degree16_18
import Definitions.Def_Sendov_FiniteRange_Degree18_20
import Definitions.Def_Sendov_FiniteRange_Degree20_22
import Definitions.Def_Sendov_FiniteRange_Degree22_24
import Definitions.Def_Sendov_FiniteRange_Degree24_26
import Definitions.Def_Sendov_FiniteRange_Degree26_27
import Definitions.Def_Sendov_FiniteRange_Degree28_29
import Definitions.Def_Sendov_FiniteRange_Degree30_31
import Definitions.Def_Sendov_FiniteRange_Degree32_33
import Definitions.Def_Sendov_FiniteRange_Degree34_35
import Definitions.Def_Sendov_FiniteRange_Degree36_37
import Definitions.Def_Sendov_FiniteRange_Degree38_39
import Definitions.Def_Sendov_FiniteRange_Degree40_41
import Definitions.Def_Sendov_FiniteRange_Degree42_43
import Definitions.Def_Sendov_FiniteRange_Degree44_45
import Definitions.Def_Sendov_FiniteRange_Degree46_47
import Definitions.Def_Sendov_FiniteRange_Degree48_49
import Definitions.Def_Sendov_FiniteRange_Degree50_51
import Definitions.Def_Sendov_FiniteRange_Degree52_53
import Definitions.Def_Sendov_FiniteRange_Degree54_55
import Definitions.Def_Sendov_FiniteRange_Degree56_58
import Definitions.Def_Sendov_FiniteRange_Degree58_60
import Definitions.Def_Sendov_FiniteRange_Degree60_63
import Definitions.Def_Sendov_FiniteRange_Degree64_69
import Definitions.Def_Sendov_FiniteRange_Degree70_79
import Definitions.Def_Sendov_FiniteRange_Degree80_100
import Definitions.Def_Sendov_FiniteRange_Cover
import Theorems.Thm_Sendov_B10_11_finite_range
import Theorems.Thm_Sendov_B12_13_finite_range
import Theorems.Thm_Sendov_B14_15_finite_range
import Theorems.Thm_Sendov_B16_18_finite_range
import Theorems.Thm_Sendov_B18_20_finite_range
import Theorems.Thm_Sendov_B20_22_finite_range
import Theorems.Thm_Sendov_B22_24_finite_range
import Theorems.Thm_Sendov_B24_26_finite_range
import Theorems.Thm_Sendov_B26_27_finite_range
import Theorems.Thm_Sendov_B28_29_finite_range
import Theorems.Thm_Sendov_B30_31_finite_range
import Theorems.Thm_Sendov_B32_33_finite_range
import Theorems.Thm_Sendov_B34_35_finite_range
import Theorems.Thm_Sendov_B36_37_finite_range
import Theorems.Thm_Sendov_B38_39_finite_range
import Theorems.Thm_Sendov_B40_41_finite_range
import Theorems.Thm_Sendov_B42_43_finite_range
import Theorems.Thm_Sendov_B44_45_finite_range
import Theorems.Thm_Sendov_B46_47_finite_range
import Theorems.Thm_Sendov_B48_49_finite_range
import Theorems.Thm_Sendov_B50_51_finite_range
import Theorems.Thm_Sendov_B52_53_finite_range
import Theorems.Thm_Sendov_B54_55_finite_range
import Theorems.Thm_Sendov_B56_58_finite_range
import Theorems.Thm_Sendov_B58_60_finite_range
import Theorems.Thm_Sendov_B60_63_finite_range
import Theorems.Thm_Sendov_B64_69_finite_range
import Theorems.Thm_Sendov_B6_6_finite_range
import Theorems.Thm_Sendov_B70_79_finite_range
import Theorems.Thm_Sendov_B80_100_finite_range
import Theorems.Thm_Sendov_B8_9_finite_range

set_option autoImplicit false
open Sendov
variable {α : ℝ}

theorem Sendov.finite_range (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 97)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) :
    R n α < 1 := by sorry
