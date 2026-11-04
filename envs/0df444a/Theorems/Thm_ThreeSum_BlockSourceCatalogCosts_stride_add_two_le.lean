-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stride_add_two_le
-- name    : ThreeSum.BlockSourceCatalogCosts.stride_add_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:56:36.066418+00:00
-- url     : https://prove2.me/theorems/88fb7f81-0847-4c3e-a14b-814a2aac6a02
-- title:
--   Block Source Catalog Costs: stride add two le
-- statement:
--   The Block Source Catalog Costs construction uses the stride add two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L30-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L30-L33

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem ThreeSum.BlockSourceCatalogCosts.stride_add_two_le (W cut : ℕ) :
    stride W cut+2 ≤ (2*W+7)*(downsetCap W cut+1) := by sorry
