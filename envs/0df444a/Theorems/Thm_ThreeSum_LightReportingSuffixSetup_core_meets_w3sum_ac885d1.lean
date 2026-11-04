-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixSetup_core_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSuffixSetup.core_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:34:04.378034+00:00
-- url     : https://prove2.me/theorems/2f9fced1-1294-411d-8819-9863b9c34ea6
-- title:
--   Light Reporting Suffix Setup: core meets
-- statement:
--   The Light Reporting Suffix Setup construction uses the core meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean#L56-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean#L56-L127

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}

theorem ThreeSum.LightReportingSuffixSetup.core_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim program 28 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,2^offset,baseL,baseR,boxBase,maskBase,work] μ (coreTime W V boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (leafWeight hfit f g stage preL preR) V ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((V+1)*downsetCap V boxCut)) := by sorry
