-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_residue_eq_iff
-- name    : ThreeSum.WantedPairs.residue_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:23.212403+00:00
-- url     : https://prove2.me/theorems/4a4efc56-cb7a-48b0-80c9-a9ebb24f380a
-- title:
--   Wanted Pairs: residue eq iff
-- statement:
--   The Wanted Pairs construction uses the residue eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L139-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L139-L143

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_LightResidueHistogram_residue_eq_iff

set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    LightResidues.residue M 1 b=LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by sorry
