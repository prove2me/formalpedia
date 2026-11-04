-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_program_meets
-- name    : ThreeSum.LightExtensionMenuMatrix.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:33:22.886828+00:00
-- url     : https://prove2.me/theorems/79ff1341-90c0-4509-a350-3dc0ea344a58
-- title:
--   Light Extension Menu Matrix: program meets
-- statement:
--   The Light Extension Menu Matrix construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuMatrix.lean#L30-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuMatrix.lean#L30-L96

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
attribute [local instance] ThreeSum.LightExtensionMenuMatrix._p2m_local_instance_68cd7abcc2_10
variable {lim : Limits}

theorem ThreeSum.LightExtensionMenuMatrix.program_meets {ctx q table logical physical J depth : ℕ}
    (C : LightExtensionQuotientPredicate.Layout) (μ : ℕ → ℤ)
    (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+9 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q)
    (H : Seg μ ctx (LightExtensionQuotientPredicate.header C))
    (hctx : ctx+10 ≤ table) (hpow : C.powers+(2*C.dim+1) ≤ table)
    (hmod : C.modulus+(C.dim+1) ≤ table)
    (htable : table+q*q ≤ logical) (hlogical : logical+q*q*(J+2) ≤ physical)
    (hphysical : physical+q*q*(J+2) ≤ C.a)
    (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (LightExtensionMultiplyTable.word q ctx C.p C.dim C.powers C.a C.b : ℤ) ≤ lim.word)
    (hcellWord : (LightExtensionMultiplyCell.word C q ctx : ℤ) ≤ lim.word)
    (hseedWord : (LightExtensionSeedMatrix.word (J+2) q C.p : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b) :
    Meets lim program 19 depth
      [q,ctx,C.p,C.dim,C.powers,C.a,C.b,table,logical,physical,J] μ (time C q J)
      (fun _ ν => (∀ r < q*q, ∀ i < J+2,
        ν (physical+r*(J+2)+i)=
          (LightExtensionSeedMatrix.value mul q C.p r (TernarySignedLayout.offset J i) : ℤ)) ∧
        Kept μ ν table) := by sorry
