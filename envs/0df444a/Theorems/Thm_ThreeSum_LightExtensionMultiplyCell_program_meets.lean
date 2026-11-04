-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
-- name    : ThreeSum.LightExtensionMultiplyCell.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:18:32.520204+00:00
-- url     : https://prove2.me/theorems/531f0d5b-5f34-452b-b06a-e82548848664
-- title:
--   Light Extension Multiply Cell: program meets
-- statement:
--   The Light Extension Multiply Cell construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyCell.lean#L127-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyCell.lean#L127-L160

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMultiplyCell
open Light LightExtensionQuotientPredicate
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
attribute [local instance] ThreeSum.LightExtensionMultiplyCell._p2m_local_instance_2d48f70718_8
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionMultiplyCell.program_meets {ctx q x y : ℕ} (C : Layout)
    (μ : ℕ → ℤ) (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+7 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q) (hx : x < q) (hy : y < q)
    (H : Seg μ ctx (header C)) (hctx : ctx+10 ≤ C.a)
    (hpow : C.powers+(2*C.dim+1) ≤ C.a)
    (hmod : C.modulus+(C.dim+1) ≤ C.a)
    (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word C q ctx : ℤ) ≤ lim.word)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (digits C.p a) (digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b)
 :
    Meets lim program 13 depth [x,y,ctx,C.p,C.dim,C.powers,C.a,C.b,q] μ (time C q)
      (fun z ν => z=(mul x y : ℤ) ∧ Kept μ ν C.a) := by sorry
