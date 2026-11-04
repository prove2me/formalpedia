-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCounts_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCounts.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:38.154206+00:00
-- url     : https://prove2.me/theorems/35c24bd0-e035-41fd-a9f4-2a4f5a9bc2b2
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean#L59-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean#L59-L178

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCounts.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+4 ≤ lim.depth)
    (hout : dst+6 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,dst,work] μ (time h)
      (fun r μ' => r = (localThreshold h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 6) := by sorry
