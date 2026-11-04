-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_rightMasks_eq_childPrefixes
-- name    : ThreeSum.LightBlockChildrenIndexed.rightMasks_eq_childPrefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:29:11.338557+00:00
-- url     : https://prove2.me/theorems/c14d58de-08ca-4672-9902-f899f5843d9a
-- title:
--   Light Block Children Indexed: right Masks eq child Prefixes
-- statement:
--   The Light Block Children Indexed construction uses the right Masks eq child Prefixes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L73-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L73-L79

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

theorem ThreeSum.LightBlockChildrenIndexed.rightMasks_eq_childPrefixes {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.rightMasks (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next =>
        subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next)) := by sorry
