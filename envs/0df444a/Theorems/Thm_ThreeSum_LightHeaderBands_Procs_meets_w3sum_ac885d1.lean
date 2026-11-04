-- Prove2me | Theorems.Thm_ThreeSum_LightHeaderBands_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightHeaderBands.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:58:18.874757+00:00
-- url     : https://prove2.me/theorems/6dbb3754-b3cc-4146-846a-6122af04b583
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHeaderBands.lean#L39-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHeaderBands.lean#L39-L64

import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513

set_option autoImplicit false
open ThreeSum ThreeSum.LightHeaderBands
open Light ThreeSum.BandEnumeration
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightHeaderBands.Procs.meets_w3sum_ac885d1 {pMain a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : At μ a nA A) (hB : At μ b nB B) (hC : At μ c nC C)
    (hAU : LightBandEnumeration.Bounded A U) (hBU : LightBandEnumeration.Bounded B U)
    (hCU : LightBandEnumeration.Bounded C U) :
    Meets lim P pMain d [a,b,c,dst] μ (time A.size B.size C.size)
      (fun r μ' => r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        LightBandEnumeration.Tables μ' dst A B C ∧ Kept μ μ' dst) := by sorry
