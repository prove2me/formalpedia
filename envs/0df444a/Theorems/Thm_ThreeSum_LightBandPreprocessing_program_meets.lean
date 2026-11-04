-- Prove2me | Theorems.Thm_ThreeSum_LightBandPreprocessing_program_meets
-- name    : ThreeSum.LightBandPreprocessing.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:48.857013+00:00
-- url     : https://prove2.me/theorems/e77099c8-b76e-4a7e-9b62-ac62b09563f2
-- title:
--   Light Band Preprocessing: program meets
-- statement:
--   The Light Band Preprocessing construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPreprocessing.lean#L239-L259
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPreprocessing.lean#L239-L259

import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightHeaderBands_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightNormalize_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSortedBands_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPreprocessing.program_meets {srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : Seg μ srcA originalA) (hBread : Seg μ srcB originalB) (hCread : Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    Meets lim program 0 d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (time originalA.length originalB.length originalC.length g)
      (fun r μ' => Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        Kept μ μ' srcA) := by sorry
