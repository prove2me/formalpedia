-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount
-- name    : ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:56:39.141422+00:00
-- url     : https://prove2.me/theorems/42ed66d4-22e8-48d9-9319-d42d77be571e
-- title:
--   Block Source Catalog Costs: count eq schedule Count
-- statement:
--   The Block Source Catalog Costs construction uses the count eq schedule Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L18-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L18-L22

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount (n : ℕ) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) =
      scheduleCount n := by sorry
