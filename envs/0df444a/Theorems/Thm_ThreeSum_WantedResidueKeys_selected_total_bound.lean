-- Prove2me | Theorems.Thm_ThreeSum_WantedResidueKeys_selected_total_bound
-- name    : ThreeSum.WantedResidueKeys.selected_total_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:57.513711+00:00
-- url     : https://prove2.me/theorems/9471e1bc-f43c-4ad0-b6fe-d32846554fb9
-- title:
--   Wanted Residue Keys: selected total bound
-- statement:
--   The Wanted Residue Keys construction uses the selected total bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L46-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L46-L49

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators

theorem ThreeSum.WantedResidueKeys.selected_total_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    M*total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR := by sorry
