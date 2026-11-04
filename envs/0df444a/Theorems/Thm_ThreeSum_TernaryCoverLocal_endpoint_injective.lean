-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective
-- name    : ThreeSum.TernaryCoverLocal.endpoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:55.582517+00:00
-- url     : https://prove2.me/theorems/14f31b43-6bda-4f04-a5bb-9b8c35fa32e8
-- title:
--   Ternary Cover Local: endpoint injective
-- statement:
--   The Ternary Cover Local construction uses the endpoint injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L40-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L40-L53

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

theorem ThreeSum.TernaryCoverLocal.endpoint_injective (α π : DigitType) :
    Function.Injective (fun e : LocalEdge L α π => (left e, right e)) := by sorry
