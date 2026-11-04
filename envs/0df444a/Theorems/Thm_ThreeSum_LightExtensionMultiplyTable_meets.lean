-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
-- name    : ThreeSum.LightExtensionMultiplyTable.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:22:24.059987+00:00
-- url     : https://prove2.me/theorems/1b0758cd-381b-4788-85c2-7e311f704fa6
-- title:
--   Light Extension Multiply Table: meets
-- statement:
--   The Light Extension Multiply Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyTable.lean#L25-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyTable.lean#L25-L107

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMultiplyTable
attribute [local instance] ThreeSum.LightExtensionMultiplyTable._p2m_local_instance_2a3ffe096f_5
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionMultiplyTable.meets {proc pCell pDigit pDivide q ctx p dim powers a b table T : ℕ}
    (hp : P[proc]?=some (body pCell pDigit pDivide))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+1 < lim.depth)
    (hq : 0 < q) (hspace : table+q*q ≤ lim.space)
    (hctxSpace : ctx ≤ lim.space) (hpowersSpace : powers ≤ lim.space)
    (haSpace : a ≤ lim.space) (hbSpace : b ≤ lim.space)
    (hword : (word q ctx p dim powers a b : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hcell : ∀ x < q, ∀ y < q, ∀ ν, Kept μ ν table →
      Meets lim P pCell (depth+1) [x,y,ctx,p,dim,powers,a,b,q] ν T
        (fun z ξ => z=(mul x y : ℤ) ∧ Kept ν ξ (table+q*q))) :
    Meets lim P proc depth [q,ctx,p,dim,powers,a,b,table] μ (time q T)
      (fun _ ν => (∀ x < q, ∀ y < q, ν (table+x*q+y)=(mul x y : ℤ)) ∧
        Kept μ ν table) := by sorry
