-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixSetup_allocate_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup.allocate_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:06:32.858306+00:00
-- url     : https://prove2.me/theorems/e8ed1fe2-f398-4c18-a91c-39e3c6855b9f
-- title:
--   allocate_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L203-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L203-L265

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup.allocate_meets {pMain pPower pPrefix pSetup pPowers pEnum m j F free d : ℕ}
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
