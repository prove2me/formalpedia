-- Prove2me | Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
-- name    : ThreeSum.LightRadixKeys.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:32.391022+00:00
-- url     : https://prove2.me/theorems/3d0abc4b-93e4-422e-b66c-ada80fc42ed4
-- title:
--   Light Radix Keys: word mono
-- statement:
--   The Light Radix Keys construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L40-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L40-L45

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightRadixKeys.word_mono {p U j k : ℕ} (hj : j ≤ k) : word p U j ≤ word p U k := by sorry
