-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorStage_program_meets
-- name    : ThreeSum.LightOriginalSurvivorStage.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:37.67299+00:00
-- url     : https://prove2.me/theorems/0f2d715e-3611-4557-9990-3a24216eaf17
-- title:
--   Light Original Survivor Stage: program meets
-- statement:
--   The Light Original Survivor Stage construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorStage.lean#L38-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorStage.lean#L38-L163

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorStage
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}

theorem ThreeSum.LightOriginalSurvivorStage.program_meets
    {keyBase n hist q out valuesBase scanBase scanN targetBase targetN powers W L U d dstValues dstKeys lengthCell : ℕ}
    (sign : ℤ) (μ : ℕ → ℤ) (keys : ℕ → ℕ) (values scan target : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeysSpace : keyBase + n ≤ out) (hhistSpace : hist + q ≤ out) (hvaluesSpace : valuesBase + n ≤ out)
    (hscanSpace : scanBase + scanN ≤ out) (htargetSpace : targetBase + targetN ≤ out) (hspace : powers + (W + 1) ≤ out)
    (hfirst : out + 2 * n ≤ dstValues) (hsecond : dstValues + n ≤ dstKeys) (hthird : dstKeys + n ≤ lengthCell)
    (hlast : lengthCell + 1 ≤ lim.space) (hword : ((targetN + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hkeys : ∀ i < n, keys i < q) (hreadKeys : ∀ i < n, μ (keyBase + i) = (keys i : ℤ))
    (hcounts : ∀ k < q, μ (hist + k) = (counts keys n k : ℤ)) (hvalues : ∀ i < n, |values i| ≤ U)
    (hreadValues : ∀ i < n, μ (valuesBase + i) = values i) (hscan : ∀ i < scanN, |scan i| ≤ U)
    (hreadScan : ∀ i < scanN, μ (scanBase + i) = scan i) (hreadTarget : ∀ i < targetN, μ (targetBase + i) = target i)
    (hsign : |sign| ≤ 1) (hvalueWord : 2 * (U : ℤ) + 3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i < j → j < targetN → target i < target j) (hL : L ≤ W) (htargetN : targetN < 2 ^ L)
    (hd : d + L + 4 ≤ lim.depth) :
    Meets lim program 7 d
      [keyBase, n, hist, q, out, valuesBase, scanBase, scanN, targetBase, targetN, powers, L, sign, dstValues, dstKeys,
        lengthCell]
      μ (time keys n scanN L)
      (fun ret ν =>
        ret =
            (LightDeletedTwoSum.flag (badIndex keys n) values scan target targetN scanN (badIndices keys n).length
                sign :
              ℤ) ∧
          ν lengthCell = ((indices keys n).length : ℤ) ∧
            Seg ν out (cells (indices keys n)) ∧
              (∀ i < (indices keys n).length, ν (dstValues + i) = values (index keys n i)) ∧
                (∀ i < (indices keys n).length, ν (dstKeys + i) = (keys (index keys n i) : ℤ)) ∧
                  Kept μ ν out ∧
                    Above μ ν lengthCell ∧ Preserves μ ν out n dstValues dstKeys (indices keys n).length lengthCell) := by sorry
