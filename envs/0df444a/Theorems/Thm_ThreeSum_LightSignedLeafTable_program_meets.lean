-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
-- name    : ThreeSum.LightSignedLeafTable.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:17:50.996231+00:00
-- url     : https://prove2.me/theorems/dee3eb04-0b62-4043-9bc7-7f392be2c7b0
-- title:
--   Light Signed Leaf Table: program meets
-- statement:
--   The Light Signed Leaf Table construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafTable.lean#L193-L219
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafTable.lean#L193-L219

import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafTable
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafTable.program_meets     {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR dst maskBase work B D d : ℕ}
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
    Meets lim program 0 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,dst,maskBase,work] μ (time W boxCut)
      (fun _ μ' => TableAt μ' dst boxCut (SignedLeaf.value f g stage preL preR) ∧
        KeptBut μ μ' maskBase dst (downsetCap W boxCut)) := by sorry
