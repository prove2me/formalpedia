-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
-- name    : ThreeSum.LightBlockChildren.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:26:59.540311+00:00
-- url     : https://prove2.me/theorems/01634988-2072-4066-8c0b-2f16e9cfd055
-- title:
--   Light Block Children: program meets
-- statement:
--   The Light Block Children construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean#L156-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean#L156-L175

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBlockChildren.program_meets {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim program 0 d
      [W,h,subsetMask Q,subsetMask A,subsetMask B,subsetMask R,masks,dstL,dstR,work]
      μ (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
        SegN μ' masks ((missingSets Q h).map subsetMask) ∧
        SegN μ' dstL (leftMasks A Q h) ∧
        SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) := by sorry
