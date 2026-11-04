-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
-- name    : ThreeSum.TernaryCoverLocal.edge_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:54.931527+00:00
-- url     : https://prove2.me/theorems/f1865dca-f7c1-4ab9-bf5c-094b56c1ef9d
-- title:
--   Ternary Cover Local: edge data
-- statement:
--   The Ternary Cover Local construction uses the edge data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L35-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L35-L38

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}

theorem ThreeSum.TernaryCoverLocal.edge_data {α π : DigitType} (e : LocalEdge L α π) :
    Edge α π (left e) (right e) (output e) := by sorry
