-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
-- name    : ThreeSum.LightTernaryEulerMemo.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:37.981771+00:00
-- url     : https://prove2.me/theorems/2c14e99e-1723-4f39-8c85-05b27e2f961a
-- title:
--   Light Ternary Euler Memo: time bound
-- statement:
--   The Light Ternary Euler Memo construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMemo.lean#L181-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMemo.lean#L181-L197

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMemo
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryEulerMemo.time_bound (N rows stages V : ℕ) :
    time N rows stages V ≤
      (stages+1)*(rows+1)*(400*(N+Nat.log 2 (V+1)+3)+500) := by sorry
