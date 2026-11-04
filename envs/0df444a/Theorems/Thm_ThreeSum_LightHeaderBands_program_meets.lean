-- Prove2me | Theorems.Thm_ThreeSum_LightHeaderBands_program_meets
-- name    : ThreeSum.LightHeaderBands.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:02:06.375778+00:00
-- url     : https://prove2.me/theorems/eeed0462-5f97-4f2d-b7f4-73205f11c9b4
-- title:
--   Light Header Bands: program meets
-- statement:
--   The Light Header Bands construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHeaderBands.lean#L73-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHeaderBands.lean#L73-L86

import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightNormalize_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSortedBands_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightHeaderBands
open Light ThreeSum.BandEnumeration
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightHeaderBands.program_meets {a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : At μ a nA A) (hB : At μ b nB B) (hC : At μ c nC C)
    (hAU : LightBandEnumeration.Bounded A U) (hBU : LightBandEnumeration.Bounded B U)
    (hCU : LightBandEnumeration.Bounded C U) :
    Meets lim program 0 d [a,b,c,dst] μ (time A.size B.size C.size)
      (fun r μ' => r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        LightBandEnumeration.Tables μ' dst A B C ∧ Kept μ μ' dst) := by sorry
