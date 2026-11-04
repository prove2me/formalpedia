-- Prove2me | Theorems.Thm_ThreeSum_WantedResidueKeys_selected_congr
-- name    : ThreeSum.WantedResidueKeys.selected_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:49.396846+00:00
-- url     : https://prove2.me/theorems/36a36ecc-6c3e-424c-8df6-df465f4cf8ca
-- title:
--   Wanted Residue Keys: selected congr
-- statement:
--   The Wanted Residue Keys construction uses the selected congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L51-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L51-L57

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators

theorem ThreeSum.WantedResidueKeys.selected_congr {M NL NR : ℕ} [NeZero M] {left left' right right' : ℕ → ℤ}
    (hleft : ∀ i < NL, left i=left' i) (hright : ∀ i < NR, right i=right' i) :
    LightOriginalOffset.selected M left right NL NR=
      LightOriginalOffset.selected M left' right' NL NR := by sorry
