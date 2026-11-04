-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices
-- name    : ThreeSum.TernaryCoverLocal.right_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:00.831484+00:00
-- url     : https://prove2.me/theorems/f2eed3d3-4bf4-4161-92a9-63e2563457a8
-- title:
--   Ternary Cover Local: right mem vertices
-- statement:
--   The Ternary Cover Local construction uses the right mem vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L64-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L64-L67

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

theorem ThreeSum.TernaryCoverLocal.right_mem_vertices {α π : DigitType} (e : LocalEdge L α π) :
    right e ∈ vertices L α := by sorry
