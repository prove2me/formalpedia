-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_fieldLeft_mem
-- name    : ThreeSum.TernaryCoverLocal.fieldLeft_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:13.928697+00:00
-- url     : https://prove2.me/theorems/a5cd7d1c-d947-4d18-9a66-ee97cfb33766
-- title:
--   Ternary Cover Local: field Left mem
-- statement:
--   The Ternary Cover Local construction uses the field Left mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L84-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L84-L86

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

theorem ThreeSum.TernaryCoverLocal.fieldLeft_mem {α π : DigitType} (e : LocalEdge L α π) :
    fieldLeft (p := p) e ∈ fieldVertices L p α := by sorry
