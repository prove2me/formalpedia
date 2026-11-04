-- Prove2me | Theorems.Thm_ThreeSum_LightZetaCell_meets_w3sum_ac885d1
-- name    : ThreeSum.LightZetaCell.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:31.558321+00:00
-- url     : https://prove2.me/theorems/d7aed91f-6177-46b6-850b-3de6195a22ae
-- title:
--   Light Zeta Cell: meets
-- statement:
--   The Light Zeta Cell construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaCell.lean#L52-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaCell.lean#L52-L162

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaCell.meets_w3sum_ac885d1 {pThis pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hThis : P[pThis]? = some (body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pThis d [L,S.card,subsetMask S,a.val,src,dst,work] μ (time L)
      (fun _ μ' => μ' (dst+subsetRank S) = Subset.zetaStep a f S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by sorry
