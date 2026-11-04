-- Prove2me | Theorems.Thm_ThreeSum_LightNaturalDot_reduced_meets
-- name    : ThreeSum.LightNaturalDot.reduced_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:54.688425+00:00
-- url     : https://prove2.me/theorems/5e3ab767-a1c9-4857-bbdf-406bb7ede145
-- title:
--   Light Natural Dot: reduced meets
-- statement:
--   The Light Natural Dot construction uses the reduced meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean#L80-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean#L80-L118

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
set_option autoImplicit false
open ThreeSum ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightNaturalDot.reduced_meets {proc pDot pDigit pDivide srcA srcB n p U V : ℕ}
    (hmain : P[proc]?=some (reducedBody pDot pDigit))
    (hdot : P[pDot]?=some body) (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ) (hw : (lim.space : ℤ)≤lim.word)
    (hd : depth+1<lim.depth)
    (hA : srcA+n≤lim.space) (hB : srcB+n≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<n, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V)
    (hword : ((20*((n+1)*(U+1)*(V+1)+p+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,p] μ (reducedTime n U V)
      (fun z ν => z=(((dot f g n)%p : ℕ) : ℤ) ∧ ν=μ) := by sorry
