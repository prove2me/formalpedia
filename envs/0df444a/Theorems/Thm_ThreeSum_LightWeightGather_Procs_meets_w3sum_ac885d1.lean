-- Prove2me | Theorems.Thm_ThreeSum_LightWeightGather_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWeightGather.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:06.869109+00:00
-- url     : https://prove2.me/theorems/7d8a36c4-8e80-4cfc-b7e4-fd066705a29f
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightGather.lean#L39-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightGather.lean#L39-L105

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightWeightGather
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightGather
open Light
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightGather.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {indices src dst N rows width : ℕ} (select : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hindices : indices+rows ≤ dst) (hsrc : src+N*width ≤ dst)
    (hspace : dst+rows*width ≤ lim.space)
    (hword : (word N rows width : ℤ) ≤ lim.word)
    (hselect : ∀ i < rows, select i < N)
    (hread : ∀ i < rows, μ (indices+i) = (select i : ℤ)) :
    Meets lim P pMain d [indices,src,dst,rows,width] μ (time rows width)
      (fun _ μ' =>
        (∀ i < rows, ∀ a < width, μ' (dst+i*width+a) = μ (src+select i*width+a)) ∧
        SameOutside μ μ' dst (rows*width)) := by sorry
