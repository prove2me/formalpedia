-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
-- name    : ThreeSum.LightPolynomialQuotientCheck.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:14.804737+00:00
-- url     : https://prove2.me/theorems/f7c9ed06-1336-4dc7-bf57-126a173e42f0
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialQuotientCheck.lean#L45-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialQuotientCheck.lean#L45-L114

import Definitions.Def_Submission_ThreeSum_LightPolynomialProductArray
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_LightPrimeAddArray
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialQuotientCheck
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightPolynomialQuotientCheck.Procs.meets {main aBase bBase hBase fBase rBase productWork sumWork d p : ℕ}
    (S : Procs P main) (μ : ℕ → ℤ) (x y h f r : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+3<lim.depth) (hp : 1<p)
    (ha : aBase+d≤productWork) (hb : bBase+d≤productWork)
    (hh : hBase+d≤productWork) (hf : fBase+(d+1)≤productWork)
    (hr : rBase+2*d≤productWork) (hprod : productWork+2*d≤sumWork)
    (hspace : sumWork+2*d≤lim.space)
    (hxRead : ∀ i<d, μ (aBase+i)=(x i : ℤ))
    (hyRead : ∀ i<d, μ (bBase+i)=(y i : ℤ))
    (hhRead : ∀ i<d, μ (hBase+i)=(h i : ℤ))
    (hfRead : ∀ i<d+1, μ (fBase+i)=(f i : ℤ))
    (hrRead : ∀ i<2*d, μ (rBase+i)=(r i : ℤ))
    (hxBound : ∀ i<d, x i<p) (hyBound : ∀ i<d, y i<p)
    (hhBound : ∀ i<d, h i<p) (hfBound : ∀ i<d+1, f i<p)
    (hrBound : ∀ i<2*d, r i<p)
    (hword : (word d p : ℤ)≤lim.word) :
    Meets lim P main depth [aBase,bBase,hBase,fBase,rBase,d,p,productWork,sumWork] μ (time d p)
      (fun z ν => z=LightPolynomialProductCheck.flag p x y (expected p d h f r) d d (2*d) ∧
        Kept μ ν productWork) := by sorry
