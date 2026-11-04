-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_mask_union
-- name    : ThreeSum.ReportingHostMasks.mask_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:40.530807+00:00
-- url     : https://prove2.me/theorems/b319fa65-6767-4921-8cbd-0b658d18f52e
-- title:
--   Reporting Host Masks: mask union
-- statement:
--   The Reporting Host Masks construction uses the mask union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L108-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L108-L110

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.mask_union {W : ℕ} (S T : Finset (Fin W)) (hd : Disjoint S T) :
    subsetMask (S ∪ T) = subsetMask S+subsetMask T := by sorry
