-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
-- name    : ThreeSum.LightExtensionQuotientSearch.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:23.980698+00:00
-- url     : https://prove2.me/theorems/4dade0a8-621a-4f63-bf23-86f7b886039f
-- title:
--   Light Extension Quotient Search: program meets
-- statement:
--   Thirteen real procedures search quotient/remainder codes. The coefficient
--   decoders and all polynomial arithmetic are included and charged on every call.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean#L34-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean#L34-L82

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionQuotientSearch._p2m_local_instance_7afa0e64b3_11

theorem ThreeSum.LightExtensionQuotientSearch.program_meets (C : Layout) {ctx q depth : ℕ}
    (μ : ℕ → ℤ) (x y f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+6<lim.depth)
    (hq : 0<q) (hp : 1<C.p)
    (H : Seg μ ctx (header C)) (hctx : ctx+10≤C.h)
    (hpowers : C.powers+(2*C.dim+1)≤C.h)
    (hpowRead : ∀ e≤2*C.dim, μ (C.powers+e)=((C.p^e : ℕ) : ℤ))
    (ha : C.a+C.dim≤C.h) (hb : C.b+C.dim≤C.h)
    (hf : C.modulus+(C.dim+1)≤C.h)
    (hh : C.h+C.dim≤C.remainder) (hr : C.remainder+2*C.dim≤C.productWork)
    (hprod : C.productWork+2*C.dim≤C.sumWork)
    (hspace : C.sumWork+2*C.dim≤lim.space)
    (hxRead : ∀ i<C.dim, μ (C.a+i)=(x i : ℤ))
    (hyRead : ∀ i<C.dim, μ (C.b+i)=(y i : ℤ))
    (hfRead : ∀ i<C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hxBound : ∀ i<C.dim, x i<C.p) (hyBound : ∀ i<C.dim, y i<C.p)
    (hfBound : ∀ i<C.dim+1, f i<C.p)
    (hword : (LightExtensionQuotientPredicate.word C.dim C.p q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word) :
    Meets lim program 12 depth [q,ctx] μ
      (q*q*(LightExtensionQuotientPredicate.time C.dim C.p q q+200)+100)
      (fun r ν => r=(LightPairSearch.first (LightPairSearch.goodCode q (good C x y f)) (q*q) : ℤ) ∧
        Kept μ ν C.h) := by sorry
