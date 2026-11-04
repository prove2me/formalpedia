-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_keys_eq_liftRows_w3sum_ac885d1
-- name    : ThreeSum.RawAKeyLists.keys_eq_liftRows_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:57.962287+00:00
-- url     : https://prove2.me/theorems/90f061bf-59be-4330-82e9-4e842ce975e0
-- title:
--   Raw AKey Lists: keys eq lift Rows
-- statement:
--   The Raw AKey Lists construction uses the keys eq lift Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L56-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L56-L69

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.keys_eq_liftRows_w3sum_ac885d1 (P : ℤ) (xs : List ℤ) :
    keys P xs=(List.finRange 3).flatMap
      (fun j => xs.map (fun x => x%P+lift j*P)) := by sorry
