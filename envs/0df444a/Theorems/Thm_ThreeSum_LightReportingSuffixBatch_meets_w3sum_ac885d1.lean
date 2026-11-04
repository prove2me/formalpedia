-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixBatch_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSuffixBatch.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:00:50.775141+00:00
-- url     : https://prove2.me/theorems/7cb8d209-7b60-4a73-8d37-054d0743b3cd
-- title:
--   Light Reporting Suffix Batch: meets
-- statement:
--   The Light Reporting Suffix Batch construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixBatch.lean#L30-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixBatch.lean#L30-L134

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBatch
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
open ReportingHostSuffix
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixBatch.meets_w3sum_ac885d1 {pMain pCell pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightReportingSuffixCell.body pLeaf pAddress))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage cardinal maskBase baseL baseR dst work B D d : ℕ}
    (hfit : offset+V ≤ W) (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ work)
    (hdst : dst+downsetCap V boxCut ≤ work) (hmasks : maskBase+masks.length ≤ work)
    (hsepL : Apart baseL ((W+1)*downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepR : Apart baseR ((W+1)*downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap V boxCut))
    (hspace : work+1+LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask V cardinal m) (hcardinal : cardinal ≤ boxCut)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work] μ (time W V masks.length)
      (fun _ μ' => TableAt μ' dst boxCut
        (LightSignedLeafBatch.values μ dst masks (leafWeight hfit f g stage preL preR)) ∧
        KeptBut μ μ' work dst (downsetCap V boxCut)) := by sorry
