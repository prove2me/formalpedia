-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_program_meets
-- name    : ThreeSum.LightExtensionMultiplyTable.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:26:18.473864+00:00
-- url     : https://prove2.me/theorems/ac6d516c-5f91-43f8-8a4b-44f0445cb3fd
-- title:
--   Light Extension Multiply Table: program meets
-- statement:
--   The Light Extension Multiply Table construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyTable.lean#L112-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyTable.lean#L112-L152

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMultiplyTable
attribute [local instance] ThreeSum.LightExtensionMultiplyTable._p2m_local_instance_2a3ffe096f_5
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionMultiplyTable.program_meets {ctx q table depth : ℕ}
    (C : LightExtensionQuotientPredicate.Layout) (μ : ℕ → ℤ)
    (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+8 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q)
    (H : Seg μ ctx (LightExtensionQuotientPredicate.header C))
    (hctx : ctx+10 ≤ table) (hpow : C.powers+(2*C.dim+1) ≤ table)
    (hmod : C.modulus+(C.dim+1) ≤ table)
    (htable : table+q*q ≤ C.a) (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word q ctx C.p C.dim C.powers C.a C.b : ℤ) ≤ lim.word)
    (hcellWord : (LightExtensionMultiplyCell.word C q ctx : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b) :
    Meets lim program 14 depth [q,ctx,C.p,C.dim,C.powers,C.a,C.b,table] μ
      (time q (LightExtensionMultiplyCell.time C q))
      (fun _ ν => (∀ x < q, ∀ y < q, ν (table+x*q+y)=(mul x y : ℤ)) ∧
        Kept μ ν table) := by sorry
