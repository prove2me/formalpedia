-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_fieldRight_mem
-- name    : ThreeSum.TernaryCoverLocal.fieldRight_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:12.107287+00:00
-- url     : https://prove2.me/theorems/41e7b5ed-ec64-4aca-9233-1cc9ffc36037
-- title:
--   Ternary Cover Local: field Right mem
-- statement:
--   The Ternary Cover Local construction uses the field Right mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L88-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L88-L90

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

theorem ThreeSum.TernaryCoverLocal.fieldRight_mem {α π : DigitType} (e : LocalEdge L α π) :
    fieldRight (p := p) e ∈ fieldVertices L p α := by sorry
