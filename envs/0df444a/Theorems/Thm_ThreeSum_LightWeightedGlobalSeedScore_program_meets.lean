-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_program_meets
-- name    : ThreeSum.LightWeightedGlobalSeedScore.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:15:12.06984+00:00
-- url     : https://prove2.me/theorems/13e33943-a215-408b-9456-66b0d38c486f
-- title:
--   Light Weighted Global Seed Score: program meets
-- statement:
--   The candidate's four scalar outputs are stored only after all its actual
--   kernels have finished. This makes the score arrays independent of scratch
--   reuse. The execution receipts below name the included concrete libraries,
--   including the actual tensor/source/count program; there is no score oracle.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L197-L291
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean#L197-L291

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Theorems.Thm_Light_LocalsBut_update
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
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalSeedScore.program_meets {lim : Limits}
    {menu seed J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
      Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
      leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
      potentialPowers flags scoreB scoreC scorePaired prefixLength R S K d
      TS TB TC TO TW TD XB XC TP H : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (μ : ℕ → ℤ) (flag collisionB collisionC paired : ℤ)
    (PB PC PO PW PX PY PZ : (ℕ → ℤ) → Prop)
    (hw : (lim.space : ℤ)≤lim.word) (hLen : J+2≤lim.space)
    (hRow : menu+seed*(J+2)≤lim.space)
    (hMod : power*p≤lim.space) (hHeader : header+104<lim.space)
    (hWanted : wanted+3*H≤lim.space) (hDivWord : ((3*H+5 : ℕ) : ℤ)≤lim.word)
    (hFlagAddr : flags+seed<lim.space) (hBAddr : scoreB+seed<lim.space)
    (hCAddr : scoreC+seed<lim.space) (hPAddr : scorePaired+seed<lim.space)
    (hFlagWord : |flag|≤lim.word) (hBWord : |collisionB|≤lim.word)
    (hCWord : |collisionC|≤lim.word) (hPWord : |paired|≤lim.word)
    (hd : d<lim.depth) (hTD : LightSmallDivide.time (3*H) 3≤TD)
    (hSpan : Meets lim LightStoredSpan.program 6 (d+1)
      [catalog,catalogRows,J,menu+seed*(J+2)] μ TS (fun r ν => r=flag ∧ ν=μ))
    (hB : Meets lim LightTernaryAppendKeys.program 6 (d+1)
      [Bmatrix,menu+seed*(J+2),Bold,Bnew,nB,J+2,p,power,hashWork] μ TB (fun _ ν => PB ν))
    (hC : ∀ ν, PB ν → Meets lim LightTernaryAppendKeys.program 6 (d+1)
      [Cmatrix,menu+seed*(J+2),Cold,Cnew,nC,J+2,p,power,hashWork] ν TC (fun _ ξ => PC ξ))
    (hO : ∀ ν, PC ν → Meets lim LightTernaryAppendKeys.program 6 (d+1)
      [Omatrix,menu+seed*(J+2),Oold,Onew,nO,J+2,p,power,hashWork] ν TO (fun _ ξ => PO ξ))
    (hW : ∀ ν, PO ν → Meets lim (LightTernaryWantedBatch.program p R S raws words maps) 4 (d+1)
      [prefixLength,Onew,positions,nO,wanted,work] ν TW
      (fun r ξ => r=((wanted+3*H : ℕ) : ℤ) ∧ PW ξ))
    (hXB : ∀ ν, PW ν → Meets lim LightOriginalCollisionScore.program 0 (d+1)
      [Bnew,nB,hist,power*p] ν XB (fun r ξ => r=collisionB ∧ PX ξ))
    (hXC : ∀ ν, PX ν → Meets lim LightOriginalCollisionScore.program 0 (d+1)
      [Cnew,nC,hist,power*p] ν XC (fun r ξ => r=collisionC ∧ PY ξ))
    (hTensor : ∀ ν, PY ν →
      Meets lim (LightWeightedGlobalTensorDriver.program xl yl zl xr yr zr K) LightWeightedGlobalTensorDriver.entry (d+1)
        [header,leftTagged,nB,rightTagged,nC,J,leftWeights,rightWeights,tensor,H,countOutput,
          quadScratch,quadPowers,potentialColumns,potentialPowers]
        (Function.update ν (header+104) (H : ℤ)) TP (fun r ξ => r=paired ∧ PZ ξ)) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 176 d
      (args menu seed J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
        Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
        leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
        potentialPowers flags scoreB scoreC scorePaired prefixLength) μ
      (time TS TB TC TO TW TD XB XC TP)
      (fun r ν => r=flag ∧ ∃ ξ, PZ ξ ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (flags+seed) flag) (scoreB+seed) collisionB) (scoreC+seed) collisionC)
          (scorePaired+seed) paired) := by sorry
