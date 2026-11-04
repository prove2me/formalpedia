-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_sum_keys_eq
-- name    : ThreeSum.RawAKeyLists.sum_keys_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:22.19818+00:00
-- url     : https://prove2.me/theorems/67e4cdc1-9d4e-4463-ae7f-fa7a4245837c
-- title:
--   Raw AKey Lists: sum keys eq
-- statement:
--   The Raw AKey Lists construction uses the sum keys eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L87-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L87-L96

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.sum_keys_eq (P : ℤ) (xs : List ℤ) (f : ℤ → ℕ) :
    (∑ i : Fin (keys P xs).length, f ((keys P xs).getD i.val 0))=
      ∑ i : Fin xs.length, ∑ j : Fin 3, f (xs.getD i.val 0%P+lift j*P) := by sorry
