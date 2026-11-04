-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_field_endpoint_injective
-- name    : ThreeSum.TernaryCoverLocal.field_endpoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:08.349337+00:00
-- url     : https://prove2.me/theorems/16f39484-3824-4b1e-a624-5c274b7f1e09
-- title:
--   Ternary Cover Local: field endpoint injective
-- statement:
--   The Ternary Cover Local construction uses the field endpoint injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L92-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L92-L97

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

theorem ThreeSum.TernaryCoverLocal.field_endpoint_injective (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π => (fieldLeft (p := p) e, fieldRight (p := p) e)) := by sorry
