-- Prove2me | Theorems.Thm_ThreeSum_LightLocalParameters_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalParameters.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:51.16037+00:00
-- url     : https://prove2.me/theorems/fd8dc962-d346-40e5-9d70-453c08304810
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalParameters.lean#L55-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalParameters.lean#L55-L127

import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalParameters
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalParameters.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+5 ≤ lim.depth)
    (hout : dst+8 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,dst,work] μ (time h)
      (fun r μ' => r = (localPrime h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 8) := by sorry
