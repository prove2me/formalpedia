-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_count_modulo
-- name    : ThreeSum.WantedPairs.count_modulo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:28.684039+00:00
-- url     : https://prove2.me/theorems/816d896a-b370-44ae-b56d-210de602d983
-- title:
--   Wanted Pairs: count modulo
-- statement:
--   The Wanted Pairs construction uses the count modulo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L145-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L145-L158

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.count_modulo (M : ℕ) (hM : 0 < M) (as bs : List ℤ) (d : ℤ) :
    count (fun i => LightResidues.residue M 1 (as.getD i 0+d))
      (fun j => LightResidues.residue M 1 (bs.getD j 0)) bs.length as.length =
      ∑ i : Fin as.length, ∑ j : Fin bs.length,
        if (M : ℤ) ∣ as.getD i.val 0+d-bs.getD j.val 0 then 1 else 0 := by sorry
