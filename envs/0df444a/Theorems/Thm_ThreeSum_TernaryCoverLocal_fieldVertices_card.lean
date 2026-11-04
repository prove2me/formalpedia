-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_fieldVertices_card
-- name    : ThreeSum.TernaryCoverLocal.fieldVertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:00.349606+00:00
-- url     : https://prove2.me/theorems/98a7d9f4-9d55-42ba-8847-6d49bdd19009
-- title:
--   Ternary Cover Local: field Vertices card
-- statement:
--   The Ternary Cover Local construction uses the field Vertices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L73-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L73-L76

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

theorem ThreeSum.TernaryCoverLocal.fieldVertices_card (α : DigitType) (hp : 2 < p) :
    (fieldVertices L p α).card = (vertices L α).card := by sorry
