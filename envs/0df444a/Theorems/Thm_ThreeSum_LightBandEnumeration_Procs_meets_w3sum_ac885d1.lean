-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandEnumeration.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:39:24.31853+00:00
-- url     : https://prove2.me/theorems/a42f2d2a-14b1-4ba0-812e-bcad1b120642
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L95-L257
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L95-L257

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandEnumeration.Procs.meets_w3sum_ac885d1 {pMain al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+width A.size B.size C.size+4 ≤ lim.depth)
    (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim P pMain d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧
        Tables μ' dst A B C ∧ Kept μ μ' dst) := by sorry
