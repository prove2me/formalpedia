-- Prove2me | Theorems.Thm_ThreeSum_LightSourceGather_program_meets
-- name    : ThreeSum.LightSourceGather.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:53:15.307605+00:00
-- url     : https://prove2.me/theorems/d5f15682-af16-4a2f-a5b3-76f066f41f30
-- title:
--   Light Source Gather: program meets
-- statement:
--   The Light Source Gather construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean#L137-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean#L137-L154

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Theorems.Thm_ThreeSum_LightSourceHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceGather.program_meets
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
    Meets lim program 0 d [raw,flags,table,dst,n,m,work] μ (time n U)
      (fun _ ν => (∀ i < n, ν (dst+i) = (value m endpoint flag hist i : ℤ)) ∧
        KeptBut μ ν work dst n) := by sorry
