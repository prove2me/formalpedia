-- Prove2me | Theorems.Thm_ThreeSum_LightZetaBatch_meets_w3sum_ac885d1
-- name    : ThreeSum.LightZetaBatch.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:51.704418+00:00
-- url     : https://prove2.me/theorems/2184b0fd-99e2-4c30-ab3c-0b5d6fd38b18
-- title:
--   Light Zeta Batch: meets
-- statement:
--   The Light Zeta Batch construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaBatch.lean#L41-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaBatch.lean#L41-L126

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaBatch.meets_w3sum_ac885d1 {pMain pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut cardinal maskBase src dst work U d : ℕ}
    (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hmasks : maskBase+masks.length ≤ work)
    (hsepSrc : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap L cut))
    (hspace : work+LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask L cardinal m) (hcardinal : cardinal ≤ cut)
    (hd : d+L+5 ≤ lim.depth) :
    Meets lim P pMain d [L,cardinal,masks.length,maskBase,a.val,src,dst,work]
      μ (time L masks.length)
      (fun _ μ' => TableAt μ' dst cut (values μ dst masks a f) ∧
        KeptBut μ μ' work dst (downsetCap L cut)) := by sorry
