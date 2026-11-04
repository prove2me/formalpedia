-- Prove2me | Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
-- name    : ThreeSum.LightSignedBoxSetup.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:34:58.132788+00:00
-- url     : https://prove2.me/theorems/40b36323-e52e-4d9e-ad9c-1dfe6ee77f2c
-- title:
--   Light Signed Box Setup: meets
-- statement:
--   The Light Signed Box Setup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedBoxSetup.lean#L24-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedBoxSetup.lean#L24-L100

import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
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
open ThreeSum ThreeSum.LightSignedBoxSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedBoxSetup.meets
    {pMain pLeafTable pBoxStages pEnumSetup pEnum pLeafBatch pLeafCell pLeaf pAddress pZetaPass pZetaBatch pZetaCell : ℕ}
    (hmain : P[pMain]? = some (body pLeafTable pBoxStages))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    (hTable : P[pLeafTable]? = some (LightSignedLeafTable.body pEnumSetup pLeafBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hLeafBatch : P[pLeafBatch]? = some (LightSignedLeafBatch.body pLeafCell))
    (hLeafCell : P[pLeafCell]? = some (LightSignedLeafCell.body pLeaf pAddress))
    (hBoxStages : P[pBoxStages]? = some (LightBoxStages.body C.pSize pZetaPass))
    (hZetaPass : P[pZetaPass]? = some (LightZetaPass.body pEnumSetup pZetaBatch))
    (hZetaBatch : P[pZetaBatch]? = some (LightZetaBatch.body pZetaCell))
    (hZetaCell : P[pZetaCell]? = some (LightZetaCell.body C.pSetup C.pOffset C.pErase C.pRank))
    {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,boxBase,maskBase,work] μ (time W boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (SignedLeaf.value f g stage preL preR) W ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((W+1)*downsetCap W boxCut)) := by sorry
