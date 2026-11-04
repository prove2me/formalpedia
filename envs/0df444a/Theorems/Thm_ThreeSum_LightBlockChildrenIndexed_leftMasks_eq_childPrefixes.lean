-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_leftMasks_eq_childPrefixes
-- name    : ThreeSum.LightBlockChildrenIndexed.leftMasks_eq_childPrefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:29.10569+00:00
-- url     : https://prove2.me/theorems/3c3b341c-5ee1-489b-9a08-8bb02b34dd83
-- title:
--   Light Block Children Indexed: left Masks eq child Prefixes
-- statement:
--   The Light Block Children Indexed construction uses the left Masks eq child Prefixes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L66-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L66-L71

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}

theorem ThreeSum.LightBlockChildrenIndexed.leftMasks_eq_childPrefixes {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.leftMasks (leftPrefix k (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next => subsetMask (leftPrefix (k+1) (prefixRows (J := J) next)) := by sorry
