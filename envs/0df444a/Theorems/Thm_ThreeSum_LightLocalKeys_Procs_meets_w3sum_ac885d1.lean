-- Prove2me | Theorems.Thm_ThreeSum_LightLocalKeys_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalKeys.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:16.25047+00:00
-- url     : https://prove2.me/theorems/bd349c1b-bce6-4f0d-98bb-e3519530b0ac
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeys.lean#L45-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeys.lean#L45-L129

import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalKeys
open Light
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalKeys.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L masks n maps rows dst free U : ℕ}
    (mask : ℕ → ℕ) (wFalse wTrue : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free L n ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hmaps : maps+rows*(2*L) ≤ dst) (hdst : dst+rows*n ≤ free)
    (hword : (word L U rows : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i)=(mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hreadFalse : ∀ j < rows, ∀ i < L, μ (maps+j*(2*L)+i)=(wFalse j i : ℤ))
    (hreadTrue : ∀ j < rows, ∀ i < L, μ (maps+j*(2*L)+L+i)=(wTrue j i : ℤ))
    (hboundFalse : ∀ j < rows, ∀ i < L, wFalse j i ≤ U)
    (hboundTrue : ∀ j < rows, ∀ i < L, wTrue j i ≤ U) :
    Meets lim P pMain d [L,masks,n,maps,rows,dst,free] μ (time L n rows)
      (fun _ ν =>
        (∀ j < rows, ∀ i < n, ν (dst+j*n+i)=
          (OneHotMask.eval (wTrue j) (fun _ => 0) L (mask i) : ℤ)-
          (OneHotMask.eval (wFalse j) (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν dst) := by sorry
