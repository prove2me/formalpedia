-- Prove2me | Theorems.Thm_ThreeSum_SourceControlLayout_stride_eq
-- name    : ThreeSum.SourceControlLayout.stride_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:28:48.435747+00:00
-- url     : https://prove2.me/theorems/bd664512-9b6b-4c82-becf-0aef0bc078c2
-- title:
--   Source Control Layout: stride eq
-- statement:
--   The Source Control Layout construction uses the stride eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlLayout.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlLayout.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceControlLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlLayout
open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress

theorem ThreeSum.SourceControlLayout.stride_eq (W cut : ℕ) :
    stride W (downsetCap W cut)=LightBlockSourceBatchLayout.stride W cut+2 := by sorry
