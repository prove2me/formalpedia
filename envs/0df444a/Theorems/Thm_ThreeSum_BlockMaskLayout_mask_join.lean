-- Prove2me | Theorems.Thm_ThreeSum_BlockMaskLayout_mask_join
-- name    : ThreeSum.BlockMaskLayout.mask_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:50.223195+00:00
-- url     : https://prove2.me/theorems/9789be46-4a86-49f9-9347-8d9505fbb6bb
-- title:
--   Block Mask Layout: mask join
-- statement:
--   The Block Mask Layout construction uses the mask join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockMaskLayout.lean#L17-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockMaskLayout.lean#L17-L27

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
set_option autoImplicit false
open ThreeSum ThreeSum.BlockMaskLayout
open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.BlockMaskLayout.mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    subsetMask (indexSet (join I rows)) = ∑ i ∈ I, rowMask rows i := by sorry
