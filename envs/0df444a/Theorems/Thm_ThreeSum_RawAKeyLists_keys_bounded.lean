-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_keys_bounded
-- name    : ThreeSum.RawAKeyLists.keys_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:47.044282+00:00
-- url     : https://prove2.me/theorems/305d3819-e990-4b8c-9e75-fbe421ca6915
-- title:
--   Raw AKey Lists: keys bounded
-- statement:
--   The Raw AKey Lists construction uses the keys bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L81-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L81-L85

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.keys_bounded {P : ℤ} (hP : 0 < P) (xs : List ℤ) :
    ∀ x ∈ keys P xs, |x| ≤ 2*P := by sorry
