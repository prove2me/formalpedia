-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentDriver_program_meets
-- name    : ThreeSum.LightWeightedGlobalMomentDriver.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:14:19.730497+00:00
-- url     : https://prove2.me/theorems/f95a77ea-c575-4a7f-b598-e4f5e7c6f127
-- title:
--   Light Weighted Global Moment Driver: program meets
-- statement:
--   Every step receipt refers to the actual included 139-procedure source
--   channel program. Those receipts come from `MomentChannelStep.Procs.meets`
--   and `MomentSourceProgram.host_meets`, which execute both original-source
--   weight initializers and the full source/count frontend.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentDriver.lean#L79-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentDriver.lean#L79-L158

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentDriver
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_take
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentDriver
open Light TernaryMomentSchedule
set_option maxHeartbeats 2000000
variable {lim : Limits} {d : ℕ}

theorem ThreeSum.LightWeightedGlobalMomentDriver.program_meets {originalB nB originalC nC leftWeight rightWeight
      matrix count out terms : ℕ} {backend : List ℤ}
    (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ))
    (cost : (ℕ×ℕ)→ℕ) (score : ℕ→ℕ→ℕ→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hwindow : matrix+terms*count≤leftWeight) (hspace : leftWeight≤lim.space)
    (htermsWord : (terms : ℤ)≤lim.word)
    (hstep : ∀ i<steps.length, ∀ ν,
      TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight
        (steps.take i) score ν →
      Meets lim (LightWeightedGlobalMomentSourceProgram.program xl yl zl xr yr zr
        (steps.getD i (0,0)).1 (steps.getD i (0,0)).2) 138 (d+1)
        (LightTernaryMomentChannelStep.args originalB nB originalC nC leftWeight rightWeight
          matrix count out backend) ν (cost (steps.getD i (0,0)))
        (fun _ ξ => TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight
          (steps.take (i+1)) score ξ)) :
    Meets lim (program xl yl zl xr yr zr steps terms (9+backend.length))
      (139*steps.length+1) d
      (LightTernaryMomentChannelStep.args originalB nB originalC nC leftWeight rightWeight
        matrix count out backend) μ
      (time steps cost terms count (9+backend.length))
      (fun _ ν => TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight steps score ν) := by sorry
