-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_work_address
-- name    : ThreeSum.BlockSourceCatalogCosts.work_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:56:04.605167+00:00
-- url     : https://prove2.me/theorems/003ddb11-ad3c-44e5-a8df-5d4c81c86086
-- title:
--   Block Source Catalog Costs: work address
-- statement:
--   The Block Source Catalog Costs construction uses the work address property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L24-L28

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem ThreeSum.BlockSourceCatalogCosts.work_address (base count W cut : ℕ) :
    LightBlockSourceBatchLayout.work base count W cut =
      base+count*(stride W cut+2)+downsetCap W cut+W+2 := by sorry
