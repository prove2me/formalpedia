-- Prove2me | Theorems.Thm_Sendov_finite_range_le_100
-- name    : Sendov.finite_range_le_100
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T20:02:12.152651+00:00
-- url     : https://prove2.me/theorems/52ac6143-1fbf-4d57-9990-8fee97550622
-- title:
--   Sendov: finite range le 100
-- statement:
--   **The finite range.**  Every degree from `5` to `100` inclusive.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Cover.lean#L58-L159
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Cover.lean#L58-L159

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

theorem Sendov.finite_range_le_100 {n : ℕ} (h0 : 5 ≤ n) (h1 : n ≤ 100)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
