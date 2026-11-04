-- Prove2me | Theorems.Thm_ThreeSum_SourceTableLayout_maskAt_lt
-- name    : ThreeSum.SourceTableLayout.maskAt_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:47.159767+00:00
-- url     : https://prove2.me/theorems/ec12e942-c90f-4ed6-9975-df3c50914866
-- title:
--   Source Table Layout: mask At lt
-- statement:
--   The Source Table Layout construction uses the mask At lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L117-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L117-L119

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000

theorem ThreeSum.SourceTableLayout.maskAt_lt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i < 2^L := by sorry
