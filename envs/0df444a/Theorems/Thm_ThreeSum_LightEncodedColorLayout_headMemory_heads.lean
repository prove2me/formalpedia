-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorLayout_headMemory_heads
-- name    : ThreeSum.LightEncodedColorLayout.headMemory_heads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:09.094829+00:00
-- url     : https://prove2.me/theorems/9baf722c-94c4-4551-812c-00a758ed0cd8
-- title:
--   Light Encoded Color Layout: head Memory heads
-- statement:
--   The Light Encoded Color Layout construction uses the head Memory heads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean#L54-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean#L54-L58

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout
set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorLayout
open Light BandPartition EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000

theorem ThreeSum.LightEncodedColorLayout.headMemory_heads (μ : ℕ → ℤ) (free n g : ℕ) :
    Seg (headMemory μ free n g) free (normalizedHeads free n g) := by sorry
