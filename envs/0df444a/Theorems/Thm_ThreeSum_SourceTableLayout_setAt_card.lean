-- Prove2me | Theorems.Thm_ThreeSum_SourceTableLayout_setAt_card
-- name    : ThreeSum.SourceTableLayout.setAt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:41.166597+00:00
-- url     : https://prove2.me/theorems/c91fb14a-f094-441a-b2b3-8518d12fffcd
-- title:
--   Source Table Layout: set At card
-- statement:
--   The Source Table Layout construction uses the set At card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L121-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L121-L124

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000

theorem ThreeSum.SourceTableLayout.setAt_card {L cut i : ℕ} (hi : i < downsetCap L cut) :
    (setAt L cut i).card ≤ cut := by sorry
