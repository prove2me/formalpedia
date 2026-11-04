-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
-- name    : ThreeSum.ReportingHostSuffix.shiftEmbedding_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:12.760556+00:00
-- url     : https://prove2.me/theorems/fa6cca13-8c67-4125-803b-c30bdf0104f7
-- title:
--   Reporting Host Suffix: shift Embedding val
-- statement:
--   The Reporting Host Suffix construction uses the shift Embedding val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L22-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L22-L23

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffix.shiftEmbedding_val {W V offset : ℕ} (hfit : offset+V ≤ W) (i : Fin V) :
    (shiftEmbedding offset hfit i).val = offset+i.val := by sorry

attribute [defeq] ThreeSum.ReportingHostSuffix.shiftEmbedding_val
