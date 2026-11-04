-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedController_program_meets
-- name    : ThreeSum.LightWeightedGlobalSeedController.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:48:37.790206+00:00
-- url     : https://prove2.me/theorems/6aef7090-ae68-4ab3-a4fb-03406e612b07
-- title:
--   Light Weighted Global Seed Controller: program meets
-- statement:
--   The seed loop calls the concrete SeedScore program for every menu entry.
--   Its final selection calls the actual integer RowSelector, reconstructs the
--   chosen seed by calling the same score program, and executes the real span
--   extension. The predicates are memory invariants between these checked calls.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedController.lean#L65-L193
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedController.lean#L65-L193

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
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
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedBatch_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedController
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalSeedController.program_meets {lim : Limits}
    {menu J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
      Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
      leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
      potentialPowers flags scoreB scoreC scorePaired prefixLength R S K d
      n U dB dC dP tB tC tP newSpan seedTime spanTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (μ : ℕ → ℤ) (flag fB fC fP : ℕ → ℤ)
    (I : ℕ → (ℕ → ℤ) → Prop) (Ready Final : (ℕ → ℤ) → Prop)
    (hw : (lim.space : ℤ)≤lim.word)
    (hFlags : flags+n≤lim.space) (hBs : scoreB+n≤lim.space)
    (hCs : scoreC+n≤lim.space) (hPs : scorePaired+n≤lim.space)
    (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP : ℤ)≤lim.word)
    (hLen : J+2≤lim.space)
    (hRow : menu+(LightTernaryRowSelector.pick
      (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1)*(J+2)≤lim.space)
    (hd : d<lim.depth) (hstart : I 0 μ)
    (hstep : ∀ i<n, ∀ ν, I i ν →
      Meets lim (LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr)
        LightWeightedGlobalSeedScore.entry (d+1)
        (LightWeightedGlobalSeedScore.args menu i J catalog catalogRows p power Bmatrix Bold Bnew nB
          Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header
          leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch quadPowers
          potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
        ν seedTime (fun _ ξ => I (i+1) ξ))
    (hread : ∀ ν, I n ν →
      (∀ i<n, ν (flags+i)=flag i ∧ |flag i|≤1) ∧
      (∀ i<n, ν (scoreB+i)=fB i ∧ |fB i|≤U) ∧
      (∀ i<n, ν (scoreC+i)=fC i ∧ |fC i|≤U) ∧
      (∀ i<n, ν (scorePaired+i)=fP i ∧ |fP i|≤U))
    (hexist : ∃ i<n, LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP i)
    (hselected : ∀ ν, I n ν →
      Meets lim (LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr)
        LightWeightedGlobalSeedScore.entry (d+1)
        (LightWeightedGlobalSeedScore.args menu (LightTernaryRowSelector.pick
          (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1)
          J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
          Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
          leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
          potentialPowers flags scoreB scoreC scorePaired prefixLength)
        ν seedTime (fun _ ξ => Ready ξ))
    (hspan : ∀ ν, Ready ν → Meets lim LightStoredSpan.program 1 (d+1)
      [catalog,catalogRows,menu+(LightTernaryRowSelector.pick
        (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1)*(J+2),newSpan,J,p]
      ν spanTime (fun _ ξ => Final ξ)) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) entry d
      (args (LightWeightedGlobalSeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB
        Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header
        leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch quadPowers
        potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
        n dB dC dP tB tC tP newSpan) μ (time n seedTime spanTime)
      (fun r ν => r=(LightTernaryRowSelector.pick
        (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n : ℤ) ∧ Final ν) := by sorry
