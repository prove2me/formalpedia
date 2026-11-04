-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryInitialKeys_time_eq
-- name    : ThreeSum.LightTernaryInitialKeys.time_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:55.185387+00:00
-- url     : https://prove2.me/theorems/a83c63ec-09f9-4d37-8833-4094cb2eaba7
-- title:
--   Light Ternary Initial Keys: time eq
-- statement:
--   The Light Ternary Initial Keys construction uses the time eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialKeys.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialKeys.lean#L49-L51

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInitialKeys
open Light
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryInitialKeys.time_eq (nB nC nO : ℕ) : time nB nC nO=13*(nB+nC+nO)+118 := by sorry
