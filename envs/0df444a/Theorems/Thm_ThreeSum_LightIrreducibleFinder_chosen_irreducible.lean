-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_chosen_irreducible
-- name    : ThreeSum.LightIrreducibleFinder.chosen_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:38.641987+00:00
-- url     : https://prove2.me/theorems/cbc5a485-7fd0-4081-8b1a-d646c1529c27
-- title:
--   Light Irreducible Finder: chosen irreducible
-- statement:
--   The Light Irreducible Finder construction uses the chosen irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L315-L326
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L315-L326

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

theorem ThreeSum.LightIrreducibleFinder.chosen_irreducible (C : Layout) [Fact C.p.Prime] (hd : 0<C.dim) :
    0<chosen C (C.p^C.dim) (C.p^C.dim) ∧
    chosen C (C.p^C.dim) (C.p^C.dim)≤C.p^C.dim ∧
    Irreducible (monicOfCode (p := C.p) C.dim (chosen C (C.p^C.dim) (C.p^C.dim)-1)) := by sorry
