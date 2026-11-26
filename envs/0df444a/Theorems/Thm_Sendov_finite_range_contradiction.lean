-- Prove2me | Theorems.Thm_Sendov_finite_range_contradiction
-- name    : Sendov.finite_range_contradiction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T20:01:53.445678+00:00
-- url     : https://prove2.me/theorems/cc857757-91d2-5879-8c9c-12ce73eb0a28
-- title:
--   Sendov: finite range contradiction
-- statement:
--   Equation `stat` of the blog post is infeasible on the range
--   `5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, `c ^ 2 ≤ A`.  This is the form in which the claim is used.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Cover.lean#L175-L178
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Cover.lean#L175-L178

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
set_option autoImplicit false
open Sendov
variable {α : ℝ}

theorem Sendov.finite_range_contradiction (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 97)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) (hstat : 1 ≤ R n α) :
    False := by sorry
