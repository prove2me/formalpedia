-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_mem_wanted
-- name    : ThreeSum.RawAKeyLists.mem_wanted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:52.880829+00:00
-- url     : https://prove2.me/theorems/eaf8c8a0-06ff-400e-9034-24acddff03fc
-- title:
--   Raw AKey Lists: mem wanted
-- statement:
--   The Raw AKey Lists construction uses the mem wanted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L125-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L125-L129

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.mem_wanted {M h J : ℕ} {P d : ℤ} {xs : List ℤ}
    {w : RawReporting.Wanted h J (Fin xs.length)} :
    w ∈ wanted M P xs h J d ↔
      (M : ℤ) ∣ xs.getD w.1.val 0%P+lift w.2.1*P+d-globalKey w.2.2 := by sorry
