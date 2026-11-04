-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
-- name    : ThreeSum.LightPrimeAddArray.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:25:50.021645+00:00
-- url     : https://prove2.me/theorems/235fcaf8-be74-464c-afe8-312b611d4d35
-- title:
--   Light Prime Add Array: meets
-- statement:
--   The Light Prime Add Array construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeAddArray.lean#L22-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeAddArray.lean#L22-L72

import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightPrimeAddArray
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeAddArray
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightPrimeAddArray.meets {proc pMulAdd pDivide srcA srcB dst n p : ℕ}
    (hp : P[proc]?=some (body pMulAdd))
    (hadd : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+1<lim.depth) (hpp : 1<p)
    (hA : srcA+n≤dst) (hB : srcB+n≤dst) (hD : dst+n≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<n, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<n, g i<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,dst,n,p] μ (time n p)
      (fun _ ν => (∀ i<n, ν (dst+i)=(((f i+g i)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst n) := by sorry
