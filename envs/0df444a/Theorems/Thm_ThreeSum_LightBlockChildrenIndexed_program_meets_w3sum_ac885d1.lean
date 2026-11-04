-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBlockChildrenIndexed.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:53:01.896569+00:00
-- url     : https://prove2.me/theorems/571412fb-e323-4a6d-b6fe-bfcae181faa7
-- title:
--   Light Block Children Indexed: program meets
-- statement:
--   The Light Block Children Indexed construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L97-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L97-L138

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}

theorem ThreeSum.LightBlockChildrenIndexed.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {h J k masks dstL dstR work d : ℕ}
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h))))
    (hp : ValidPrefix q k pre) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hmasks : masks+groupSize h ≤ dstL)
    (hleft : dstL+groupSize h ≤ dstR)
    (hright : dstR+groupSize h ≤ work)
    (hspace : work+(2*(J*(512*h))+2) ≤ lim.space)
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+3 ≤ lim.depth) :
    Meets lim LightBlockChildren.program 0 d
      [J*(512*h),h,rowMask (outputRows q) ⟨k,hk⟩,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows q)),masks,dstL,dstR,work]
      μ (LightBlockChildren.time (J*(512*h)) (2*h) h)
      (fun r μ' =>
        r = (subsetMask (querySet (k+1) (outputRows q)) : ℤ) ∧
        SegN μ' masks ((globalChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h).map subsetMask) ∧
        SegN μ' dstL ((childPrefixes q pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN μ' dstR ((childPrefixes q pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next))) ∧
        Kept μ μ' masks) := by sorry
