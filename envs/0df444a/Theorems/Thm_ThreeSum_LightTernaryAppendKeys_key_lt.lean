-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryAppendKeys_key_lt
-- name    : ThreeSum.LightTernaryAppendKeys.key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:17.565714+00:00
-- url     : https://prove2.me/theorems/76ed85c4-cfe4-4b64-a676-3997b5d23167
-- title:
--   Light Ternary Append Keys: key lt
-- statement:
--   The Light Ternary Append Keys construction uses the key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryAppendKeys.lean#L131-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryAppendKeys.lean#L131-L135

import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryAppendKeys
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryAppendKeys.key_lt (p power len : ℕ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ)
    (hp : 0<p) (ho : old i<power) : key p power len old z c i<power*p := by sorry
