-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stageCellCount_eq
-- name    : ThreeSum.BlockSourceCatalogCosts.stageCellCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:56:47.604277+00:00
-- url     : https://prove2.me/theorems/e907f33f-bc66-40c7-9c20-eaf460e4b0c9
-- title:
--   Block Source Catalog Costs: stage Cell Count eq
-- statement:
--   The Block Source Catalog Costs construction uses the stage Cell Count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L47-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L47-L52

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem ThreeSum.BlockSourceCatalogCosts.stageCellCount_eq (n : ℕ) :
    stageCellCount n = 2*bandCount n*scheduleCount n*(256*mu n+1)*
      downsetCap (256*mu n) (mu n) := by sorry
