-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
-- name    : ThreeSum.LightExtensionSeedRow.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:21.719199+00:00
-- url     : https://prove2.me/theorems/ca70f872-692c-4520-a350-a43ee595f521
-- title:
--   Light Extension Seed Row: meets
-- statement:
--   The Light Extension Seed Row construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionSeedRow.lean#L38-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionSeedRow.lean#L38-L122

import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionSeedRow
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionSeedRow.meets {proc pDigit pDivide table q p x y dst len : ℕ}
    (hp : P[proc]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+1<lim.depth)
    (hx : x<q) (hy : y<q) (hmod : 0<p)
    (htable : table+q*q≤dst) (hspace : dst+len≤lim.space)
    (hread : ∀ a<q, ∀ b<q, μ (table+a*q+b)=(mul a b : ℤ))
    (hmul : ∀ a<q, ∀ b<q, mul a b<q)
    (hword : (word len q p : ℤ)≤lim.word) :
    Meets lim P proc depth [table,q,p,x,y,dst,len] μ (time len q)
      (fun z ν => z=(trajectory mul x y len : ℤ) ∧
        (∀ i<len, ν (dst+i)=(((trajectory mul x y i)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst len) := by sorry
