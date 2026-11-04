-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
-- name    : ThreeSum.LightTernaryEulerRow.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:16.228204+00:00
-- url     : https://prove2.me/theorems/68271af0-e9e5-4686-aca5-e27dc9eb1390
-- title:
--   Light Ternary Euler Row: time bound
-- statement:
--   The Light Ternary Euler Row construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean#L81-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean#L81-L85

import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryEulerRow.time_bound (N V : ℕ) :
    time N V ≤ 400*(N+Nat.log 2 (V+1)+3) := by sorry
