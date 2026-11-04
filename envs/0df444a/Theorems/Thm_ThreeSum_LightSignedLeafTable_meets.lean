-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
-- name    : ThreeSum.LightSignedLeafTable.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:28:43.655606+00:00
-- url     : https://prove2.me/theorems/6ce21162-729b-4828-9764-64c4a4885cf7
-- title:
--   Light Signed Leaf Table: meets
-- statement:
--   The Light Signed Leaf Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafTable.lean#L46-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafTable.lean#L46-L159

import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
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
open ThreeSum ThreeSum.LightSignedLeafTable
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafTable.meets {pMain pEnumSetup pEnum pBatch pCell pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightSignedLeafBatch.body pCell))
    (hCell : P[pCell]? = some (LightSignedLeafCell.body pLeaf pAddress))
    {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR dst maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdst : dst+downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hsepL : Apart baseL ((W+1)*downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hsepR : Apart baseR ((W+1)*downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,dst,maskBase,work] μ (time W boxCut)
      (fun _ μ' => TableAt μ' dst boxCut (SignedLeaf.value f g stage preL preR) ∧
        KeptBut μ μ' maskBase dst (downsetCap W boxCut)) := by sorry
