-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_wantedCount_eq_guardedCount
-- name    : ThreeSum.RawAKeyLists.wantedCount_eq_guardedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:50.776303+00:00
-- url     : https://prove2.me/theorems/bb9739c5-3a63-4a11-9527-5b31dd962925
-- title:
--   Raw AKey Lists: wanted Count eq guarded Count
-- statement:
--   The Raw AKey Lists construction uses the wanted Count eq guarded Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L102-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L102-L106

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.wantedCount_eq_guardedCount (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    GlobalKeyOffset.wantedCount M (keys P xs) h J d=guardedCount M P xs h J d := by sorry
