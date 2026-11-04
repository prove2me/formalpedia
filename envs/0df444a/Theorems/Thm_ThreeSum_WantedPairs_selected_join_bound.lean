-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_selected_join_bound
-- name    : ThreeSum.WantedPairs.selected_join_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:11.940133+00:00
-- url     : https://prove2.me/theorems/4bfcc39a-a531-44fd-9eb9-2e483893e756
-- title:
--   Wanted Pairs: selected join bound
-- statement:
--   The Wanted Pairs construction uses the selected join bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L173-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L173-L181

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.selected_join_bound (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    M*count
      (fun i => LightResidues.residue M 1
        ((RawAKeyLists.keys P xs).getD i 0+RawAKeyLists.selected M P xs h J))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length (RawAKeyLists.keys P xs).length ≤
      3*xs.length*(GlobalEncoding.scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by sorry
