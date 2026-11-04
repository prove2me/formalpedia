-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
-- name    : ThreeSum.LightPolynomialProductArray.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:43.634564+00:00
-- url     : https://prove2.me/theorems/c0168fa6-09eb-4237-bb4c-68b550d9e761
-- title:
--   Light Polynomial Product Array: meets
-- statement:
--   The Light Polynomial Product Array construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductArray.lean#L23-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductArray.lean#L23-L77

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductArray
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductArray
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightPolynomialProductArray.meets {proc pCoefficient pRaw pDigit pDivide srcA srcB dst n m len p : ℕ}
    (hp : P[proc]?=some (body pCoefficient))
    (hcoeff : P[pCoefficient]?=some (LightPolynomialCoefficient.reducedBody pRaw pDigit))
    (hraw : P[pRaw]?=some LightPolynomialCoefficient.body)
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth)
    (hA : srcA+n≤dst) (hB : srcB+m≤dst) (hD : dst+len≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : ((20*((n+1)*(p+1)^2+len+m+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,m,len,p,dst] μ (time n p len)
      (fun _ ν => (∀ k<len, ν (dst+k)=(LightPolynomialCoefficient.coefficient p f g n m k : ℤ)) ∧
        SameOutside μ ν dst len) := by sorry
