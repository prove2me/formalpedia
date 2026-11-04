-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_work_le_encoderCount_w3sum_ac885d1
-- name    : ThreeSum.BlockSourceCatalogCosts.work_le_encoderCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:09:38.548875+00:00
-- url     : https://prove2.me/theorems/8db664f5-bf1d-478b-906c-b75574ee61f4
-- title:
--   Block Source Catalog Costs: work le encoder Count
-- statement:
--   The Block Source Catalog Costs construction uses the work le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L65-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L65-L87

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceStageCosts_work_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem ThreeSum.BlockSourceCatalogCosts.work_le_encoderCount_w3sum_ac885d1 (n : ℕ) :
    work n ≤ LightBlockSourceCatalogProgram.factor
      (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)*encoderCount n := by sorry
