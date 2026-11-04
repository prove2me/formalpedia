-- Prove2me | Theorems.Thm_ThreeSum_LightSourceGather_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceGather.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:52.666975+00:00
-- url     : https://prove2.me/theorems/8dc172ac-355c-4ffa-aa12-6f9336cd42be
-- title:
--   Light Source Gather: meets
-- statement:
--   The Light Source Gather construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean#L48-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean#L48-L133

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceGather.meets_w3sum_ac885d1 {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {raw flags table dst n m work U B : ℕ}
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hm : 0 < m)
    (hraw : raw+n ≤ dst) (hflags : flags+n ≤ dst) (htable : table+m ≤ dst)
    (hdst : dst+n ≤ work) (hspace : work+(Nat.log 2 (U+1)+2) ≤ lim.space)
    (hword : (4*U+4*m+16 : ℤ) ≤ lim.word) (hcountWord : (B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (U : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw,flags,table,dst,n,m,work] μ (time n U)
      (fun _ ν => (∀ i < n, ν (dst+i) = (value m endpoint flag hist i : ℤ)) ∧
        KeptBut μ ν work dst n) := by sorry
