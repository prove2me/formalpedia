-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
-- name    : ThreeSum.LightBandEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:42:35.849165+00:00
-- url     : https://prove2.me/theorems/f4622137-ebcb-45c6-87a4-0644b38ca4f4
-- title:
--   Light Band Enumeration: program meets
-- statement:
--   The Light Band Enumeration construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L265-L279
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L265-L279

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandEnumeration.program_meets {al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+width A.size B.size C.size+4 ≤ lim.depth)
    (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim program 0 d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧
        Tables μ' dst A B C ∧ Kept μ μ' dst) := by sorry
