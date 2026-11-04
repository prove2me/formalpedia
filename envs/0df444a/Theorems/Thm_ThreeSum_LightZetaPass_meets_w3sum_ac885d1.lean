-- Prove2me | Theorems.Thm_ThreeSum_LightZetaPass_meets_w3sum_ac885d1
-- name    : ThreeSum.LightZetaPass.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:27:45.101482+00:00
-- url     : https://prove2.me/theorems/17e1f504-75ab-4aa1-aa0b-2dbf50c49a9d
-- title:
--   Light Zeta Pass: meets
-- statement:
--   The Light Zeta Pass construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L54-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L54-L152

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaPass.meets_w3sum_ac885d1
    {pMain pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ L)
    (hsrc : src+downsetCap L cut ≤ maskBase) (hdst : dst+downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,a.val,src,dst,maskBase,work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧
        KeptBut μ μ' maskBase dst (downsetCap L cut)) := by sorry
