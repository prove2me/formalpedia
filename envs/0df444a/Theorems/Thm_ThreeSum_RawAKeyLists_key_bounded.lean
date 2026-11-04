-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_key_bounded
-- name    : ThreeSum.RawAKeyLists.key_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:02.904717+00:00
-- url     : https://prove2.me/theorems/7bfaf74c-a451-4bac-a6be-0a670eed12e5
-- title:
--   Raw AKey Lists: key bounded
-- statement:
--   The Raw AKey Lists construction uses the key bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L71-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L71-L79

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.key_bounded {P : ℤ} (hP : 0 < P) (xs : List ℤ) (r : Record xs) :
    |key P xs r| ≤ 2*P := by sorry
