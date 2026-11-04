-- Prove2me | Theorems.Thm_ThreeSum_SourceTableLayout_maskAt_mem
-- name    : ThreeSum.SourceTableLayout.maskAt_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:27.823099+00:00
-- url     : https://prove2.me/theorems/6b3af85b-a660-4b7c-9ec2-be1564ec3875
-- title:
--   Source Table Layout: mask At mem
-- statement:
--   The Source Table Layout construction uses the mask At mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L111-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L111-L115

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000

theorem ThreeSum.SourceTableLayout.maskAt_mem {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i ∈ enumerateDownset L cut := by sorry
