-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_allocate_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.allocate_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:38.721593+00:00
-- url     : https://prove2.me/theorems/e7d8bdd1-f47d-4f05-a047-13705a7186b5
-- title:
--   Light Weighted Global Prefix Setup: allocate meets
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the allocate meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L203-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L203-L265

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedGlobalPrefixSetup.allocate_meets {pMain pPower pPrefix pSetup pPowers pEnum m j F free d : ℕ}
    (hmain : P[pMain]?=some (allocateBody pPower pPrefix))
    (hpower : P[pPower]?=some LightNatPower.body)
    (hprefix : P[pPrefix]?=some (body pPower pSetup))
    (hsetup : P[pSetup]?=some (LightWeightedEnumerationSetup.body pPowers pEnum))
    (hpowers : P[pPowers]?=some powTableBody)
    (henum : P[pEnum]?=some (LightCacheEnumeration.body pEnum))
    (μ : ℕ→ ℤ) (hw : (lim.space:ℤ)≤ lim.word)
    (hspace : endAt free m j≤ lim.space) (hword : (word m j F:ℤ)≤ lim.word)
    (hd : d+N m j+4≤ lim.depth) :
    Meets lim P pMain d [j,m,F,free] μ (allocateTime m j)
      (fun r ν=>r=(headerAt free m j:ℤ) ∧
        Seg ν (headerAt free m j) (header m j F free (workAt free m j)) ∧
        Seg ν free ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν (workAt free m j) (2*N m j) ∧ Kept μ ν free) := by sorry
