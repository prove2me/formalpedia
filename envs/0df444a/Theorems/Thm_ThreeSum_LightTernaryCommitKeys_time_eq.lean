-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCommitKeys_time_eq
-- name    : ThreeSum.LightTernaryCommitKeys.time_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:57.544659+00:00
-- url     : https://prove2.me/theorems/be902a09-54ed-4c51-a861-65ba5e2fdd92
-- title:
--   Light Ternary Commit Keys: time eq
-- statement:
--   The Light Ternary Commit Keys construction uses the time eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitKeys.lean#L63-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitKeys.lean#L63-L65

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCommitKeys
open Light
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryCommitKeys.time_eq (nB nC nO : ℕ) : time nB nC nO=16*(nB+nC+nO)+118 := by sorry
