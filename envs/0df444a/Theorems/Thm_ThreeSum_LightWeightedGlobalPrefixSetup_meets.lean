-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:04.169984+00:00
-- url     : https://prove2.me/theorems/02d0721d-e8fe-4b29-bb6c-036d73303e26
-- title:
--   Light Weighted Global Prefix Setup: meets
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L65-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L65-L159

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedGlobalPrefixSetup.meets {pMain pPower pSetup pPowers pEnum m j F dst bank work d : ℕ}
    (hmain : P[pMain]?=some (body pPower pSetup))
    (hpower : P[pPower]?=some LightNatPower.body)
    (hsetup : P[pSetup]?=some (LightWeightedEnumerationSetup.body pPowers pEnum))
    (hpowers : P[pPowers]?=some powTableBody)
    (henum : P[pEnum]?=some (LightCacheEnumeration.body pEnum))
    (μ : ℕ→ ℤ) (hw : (lim.space:ℤ)≤ lim.word)
    (hbank : bank+nb m j≤ work) (hwork : work+(2*N m j+1)≤ dst)
    (hspace : dst+8≤ lim.space) (hword : (word m j F:ℤ)≤ lim.word)
    (hd : d+N m j+3≤ lim.depth) :
    Meets lim P pMain d [j,m,F,dst,bank,work] μ (time m j)
      (fun r ν=>r=(dst:ℤ) ∧ Seg ν dst (header m j F bank work) ∧
        Seg ν bank ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν work (2*N m j) ∧ Kept μ ν bank) := by sorry
