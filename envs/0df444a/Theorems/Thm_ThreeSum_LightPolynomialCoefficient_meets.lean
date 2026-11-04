-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
-- name    : ThreeSum.LightPolynomialCoefficient.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:20.541985+00:00
-- url     : https://prove2.me/theorems/b11108bb-b0de-4ad5-9d0f-1e1a101e03e6
-- title:
--   Light Polynomial Coefficient: meets
-- statement:
--   The Light Polynomial Coefficient construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L53-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L53-L130

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightPolynomialCoefficient.meets {proc srcA srcB n m k p : ℕ}
    (hp : P[proc]?=some body) (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hA : srcA+n≤lim.space) (hB : srcB+m≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : (((n+1)*(p+1)^2+k+m+10 : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,m,k] μ (time n)
      (fun r ν => r=(rawCoefficient f g n m k : ℤ) ∧ ν=μ) := by sorry
