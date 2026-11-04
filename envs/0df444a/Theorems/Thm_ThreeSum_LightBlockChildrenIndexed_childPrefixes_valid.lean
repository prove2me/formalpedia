-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childPrefixes_valid
-- name    : ThreeSum.LightBlockChildrenIndexed.childPrefixes_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:26.322101+00:00
-- url     : https://prove2.me/theorems/4431f45e-ba36-4904-b5ce-ef431f56a68d
-- title:
--   Light Block Children Indexed: child Prefixes valid
-- statement:
--   The Light Block Children Indexed construction uses the child Prefixes valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L25-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L25-L30

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

theorem ThreeSum.LightBlockChildrenIndexed.childPrefixes_valid {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (next : List (Finset (Fin (512*h)))) (hn : next ∈ childPrefixes q pre hk) :
    ValidPrefix q (k+1) next := by sorry
