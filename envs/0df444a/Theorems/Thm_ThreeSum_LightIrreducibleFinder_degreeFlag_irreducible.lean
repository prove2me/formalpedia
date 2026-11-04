-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_degreeFlag_irreducible
-- name    : ThreeSum.LightIrreducibleFinder.degreeFlag_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:33.437212+00:00
-- url     : https://prove2.me/theorems/0bd09ed6-8ea4-4e47-a5c8-a8131c2f191b
-- title:
--   Light Irreducible Finder: degree Flag irreducible
-- statement:
--   The Light Irreducible Finder construction uses the degree Flag irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L158-L189
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L158-L189

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits}
open TernaryExtensionEncoding

theorem ThreeSum.LightIrreducibleFinder.degreeFlag_irreducible (C : Layout) [Fact C.p.Prime] {c : ℕ}
    (hd : 0<C.dim) (hc : c<C.p^C.dim) :
    degreeFlag C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) (C.dim-1)=1 ↔
      Irreducible (monicOfCode (p := C.p) C.dim c) := by sorry
