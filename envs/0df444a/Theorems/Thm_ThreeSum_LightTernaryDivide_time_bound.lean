-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
-- name    : ThreeSum.LightTernaryDivide.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:40:05.338424+00:00
-- url     : https://prove2.me/theorems/dc21eb31-992d-418c-b871-d3758c0fa763
-- title:
--   Light Ternary Divide: time bound
-- statement:
--   The Light Ternary Divide construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryDivide.lean#L73-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryDivide.lean#L73-L75

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Mathlib.Data.Int.Order.Lemmas
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryDivide.time_bound (V : ℕ) : time V ≤ 200*(Nat.log 2 (V+1)+2) := by sorry
