-- Prove2me | Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
-- name    : ThreeSum.LightCanonicalBoxSum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:17:53.866967+00:00
-- url     : https://prove2.me/theorems/5f2c5417-d168-4a80-b537-b982a41d2a3c
-- title:
--   Light Canonical Box Sum: program meets
-- statement:
--   The Light Canonical Box Sum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCanonicalBoxSum.lean#L155-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCanonicalBoxSum.lean#L155-L171

import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCanonicalBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCanonicalBoxSum.program_meets {μ : ℕ → ℤ} {W cut t base maskBase work B d : ℕ}
    (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W)
    (hdata : base+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+Q.card.choose t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((Q.card.choose t*(2^W*B) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hflags : Q.card-t ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim program 0 d [W,cut,Q.card,subsetMask Q,t,base,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        KeptBut μ μ' work maskBase (Q.card.choose t)) := by sorry
