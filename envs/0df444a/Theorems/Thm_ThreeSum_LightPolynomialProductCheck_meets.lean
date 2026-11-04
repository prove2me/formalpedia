-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
-- name    : ThreeSum.LightPolynomialProductCheck.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:29.51152+00:00
-- url     : https://prove2.me/theorems/365d873b-6e67-4a9d-bce8-703457803100
-- title:
--   Light Polynomial Product Check: meets
-- statement:
--   The Light Polynomial Product Check construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L49-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L49-L123

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightPolynomialProductCheck.meets {proc pCoefficient pRaw pDigit pDivide srcA srcB dst n m len p : ℕ}
    (hp : P[proc]?=some (body pCoefficient))
    (hcoeff : P[pCoefficient]?=some (LightPolynomialCoefficient.reducedBody pRaw pDigit))
    (hraw : P[pRaw]?=some LightPolynomialCoefficient.body)
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g expected : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth)
    (hA : srcA+n≤lim.space) (hB : srcB+m≤lim.space) (hD : dst+len≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hreadD : ∀ i<len, μ (dst+i)=(expected i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : ((20*((n+1)*(p+1)^2+len+m+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,dst,n,m,len,p] μ (time n p len)
      (fun r ν => r=flag p f g expected n m len ∧ ν=μ) := by sorry
