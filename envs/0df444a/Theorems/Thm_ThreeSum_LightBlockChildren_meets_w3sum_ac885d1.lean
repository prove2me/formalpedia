-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildren_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBlockChildren.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:24:48.331866+00:00
-- url     : https://prove2.me/theorems/3f84f850-6aed-4a5c-8c6d-1c043645cef9
-- title:
--   Light Block Children: meets
-- statement:
--   The Light Block Children construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean#L51-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean#L51-L148

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBlockChildren.meets_w3sum_ac885d1 {pMain pEnum pAffine : ℕ}
    (hmain : P[pMain]? = some (body pEnum pAffine)) (C : Procs P pEnum pAffine)
    {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
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
    Meets lim P pMain d
      [W,h,subsetMask Q,subsetMask A,subsetMask B,subsetMask R,masks,dstL,dstR,work]
      μ (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
        SegN μ' masks ((missingSets Q h).map subsetMask) ∧
        SegN μ' dstL (leftMasks A Q h) ∧
        SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) := by sorry
