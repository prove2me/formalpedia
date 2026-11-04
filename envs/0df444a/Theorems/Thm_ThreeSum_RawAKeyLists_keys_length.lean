-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_keys_length
-- name    : ThreeSum.RawAKeyLists.keys_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:59.567686+00:00
-- url     : https://prove2.me/theorems/325132d7-c7ca-445b-a1b7-65cb83d118ae
-- title:
--   Raw AKey Lists: keys length
-- statement:
--   The Raw AKey Lists construction uses the keys length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L40-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L40-L41

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.keys_length (P : ℤ) (xs : List ℤ) : (keys P xs).length=3*xs.length := by sorry
