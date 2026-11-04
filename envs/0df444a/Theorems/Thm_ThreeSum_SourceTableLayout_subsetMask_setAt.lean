-- Prove2me | Theorems.Thm_ThreeSum_SourceTableLayout_subsetMask_setAt
-- name    : ThreeSum.SourceTableLayout.subsetMask_setAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:00.211428+00:00
-- url     : https://prove2.me/theorems/1aba2054-ed74-4625-a9e2-3561787241cb
-- title:
--   Source Table Layout: subset Mask set At
-- statement:
--   The Source Table Layout construction uses the subset Mask set At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L126-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L126-L128

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000

theorem ThreeSum.SourceTableLayout.subsetMask_setAt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    subsetMask (setAt L cut i) = maskAt L cut i := by sorry
