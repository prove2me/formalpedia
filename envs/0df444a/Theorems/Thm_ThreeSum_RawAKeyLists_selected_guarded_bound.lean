-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_selected_guarded_bound
-- name    : ThreeSum.RawAKeyLists.selected_guarded_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:39.328779+00:00
-- url     : https://prove2.me/theorems/dcdcc638-7e58-4ee4-9b66-e56e43213702
-- title:
--   Raw AKey Lists: selected guarded bound
-- statement:
--   The Raw AKey Lists construction uses the selected guarded bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L114-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L114-L118

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.selected_guarded_bound (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    M*guardedCount M P xs h J (selected M P xs h J) ≤
      3*xs.length*(scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by sorry
