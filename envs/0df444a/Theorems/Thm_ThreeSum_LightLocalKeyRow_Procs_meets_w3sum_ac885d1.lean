-- Prove2me | Theorems.Thm_ThreeSum_LightLocalKeyRow_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalKeyRow.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:40.379359+00:00
-- url     : https://prove2.me/theorems/348f3aee-8128-44fd-a988-21df128da291
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeyRow.lean#L50-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeyRow.lean#L50-L139

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalKeyRow
open Light LightSubsetAddress
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalKeyRow.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L masks n srcFalse srcTrue free U : ℕ}
    (mask wFalse wTrue : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hspace : space free L n ≤ lim.space)
    (hmasks : masks+n ≤ free) (hfalse : srcFalse+L ≤ free) (htrue : srcTrue+L ≤ free)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hreadFalse : ∀ i < L, μ (srcFalse+i) = (wFalse i : ℤ))
    (hreadTrue : ∀ i < L, μ (srcTrue+i) = (wTrue i : ℤ))
    (hboundFalse : ∀ i < L, wFalse i ≤ U) (hboundTrue : ∀ i < L, wTrue i ≤ U) :
    Meets lim P pMain d [L,masks,n,srcFalse,srcTrue,free] μ (time L n)
      (fun r ν => r=((free+L : ℕ) : ℤ) ∧
        (∀ i < n, ν (free+L+i) =
          (OneHotMask.eval wTrue (fun _ => 0) L (mask i) : ℤ)-
          (OneHotMask.eval wFalse (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν free) := by sorry
