-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialCoefficient_reduced_meets
-- name    : ThreeSum.LightPolynomialCoefficient.reduced_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:48.23611+00:00
-- url     : https://prove2.me/theorems/56bfe0c5-0c4a-4b15-8c45-192cc920a3d6
-- title:
--   Light Polynomial Coefficient: reduced meets
-- statement:
--   The Light Polynomial Coefficient construction uses the reduced meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L138-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L138-L180

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightPolynomialCoefficient.reduced_meets {proc pRaw pDigit pDivide srcA srcB n m k p : ℕ}
    (hp : P[proc]?=some (reducedBody pRaw pDigit))
    (hraw : P[pRaw]?=some body)
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+1<lim.depth)
    (hA : srcA+n≤lim.space) (hB : srcB+m≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : ((20*((n+1)*(p+1)^2+k+m+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,m,k,p] μ (reducedTime n p)
      (fun r ν => r=(coefficient p f g n m k : ℤ) ∧ ν=μ) := by sorry
