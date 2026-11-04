-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedBatch_program_meets
-- name    : ThreeSum.LightTernaryWantedBatch.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:27:35.591107+00:00
-- url     : https://prove2.me/theorems/55a27ebb-633c-45b7-b361-a564b867ccbe
-- title:
--   Light Ternary Wanted Batch: program meets
-- statement:
--   The Light Ternary Wanted Batch construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBatch.lean#L48-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBatch.lean#L48-L121

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBatch
open Light LightTernaryWantedCanonical
open TernaryWantedLittleEndian (wantedCodes)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits}

theorem ThreeSum.LightTernaryWantedBatch.program_meets {P R S C V work J d targetBase positionBase n dst : ℕ}
    {raws : List ℤ} {words maps : List ℕ}
    (hp : 2≤P) (hN : 1≤raws.length) (hR : 1≤R) (hS : 1≤S) (hC : 1≤C)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (P : ℤ) raws x).length≤C)
    (hraw : ∀ i<raws.length, |raws.getD i 0|≤(V : ℤ))
    (hwords : ∀ i<raws.length, words.getD i 0<R)
    (hmaps : ∀ i<raws.length, maps.getD i 0<S)
    (hRW : (R : ℤ)≤lim.word) (hSW : (S : ℤ)≤lim.word)
    (hNW : (raws.length : ℤ)≤lim.word) (F : Emod.Pre lim P (2*V) work)
    (μ : ℕ → ℤ) (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (htarget : targetBase+n≤dst) (hpositions : positionBase+n≤dst)
    (htRead : ∀ i<n, μ (targetBase+i)=targets i)
    (hpRead : ∀ i<n, μ (positionBase+i)=(positions i : ℤ))
    (htBound : ∀ i<n, |targets i|≤(V : ℤ))
    (hc : (((2*R)^J : ℕ) : ℤ)≤lim.word) (hm : (((2*S)^J : ℕ) : ℤ)≤lim.word)
    (ho : ∀ i<n, (positions i : ℤ)≤lim.word) (hJ : (J : ℤ)≤lim.word)
    (hs : dst+3*n*C^J≤work) (hd : d+J+4≤lim.depth) :
    Meets lim (program P R S raws words maps) 4 d
      [J,targetBase,positionBase,n,dst,work] μ (time P C V J n)
      (fun r ν => r=((dst+(rows P R S J raws words maps targets positions n).length : ℕ) : ℤ) ∧
        Seg ν dst (rows P R S J raws words maps targets positions n) ∧ Kept μ ν dst) := by sorry
