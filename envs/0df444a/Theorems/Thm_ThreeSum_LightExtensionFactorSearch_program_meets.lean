-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionFactorSearch_program_meets
-- name    : ThreeSum.LightExtensionFactorSearch.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:22.936628+00:00
-- url     : https://prove2.me/theorems/2ddfbc2f-6ace-4638-8cb4-c376532fb407
-- title:
--   Light Extension Factor Search: program meets
-- statement:
--   Ten actual procedures search all properly bounded monic factor codes.
--   The exhaustive loops include coefficient decoding and product checks.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorSearch.lean#L35-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorSearch.lean#L35-L70

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionFactorSearch._p2m_local_instance_9c16afeb32_9

theorem ThreeSum.LightExtensionFactorSearch.program_meets (C : Layout) {ctx q depth : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+6<lim.depth)
    (hq : 0<q) (hp : 1<C.p) (he : 0<C.degree) (hed : C.degree<C.dim)
    (H : Seg μ ctx (header C)) (hctx : ctx+7≤C.left)
    (hpow : C.powers+(2*C.dim+1)≤C.left)
    (htarget : C.target+2*C.dim≤C.left) (hleft : C.left+2*C.dim≤C.right)
    (hspace : C.right+2*C.dim≤lim.space)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*C.dim, μ (C.target+i)=(f i : ℤ))
    (hword : (word C q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word) :
    Meets lim program 9 depth [q,ctx] μ
      (q*q*(time C q q+200)+100)
      (fun r ν => r=(LightPairSearch.first (LightPairSearch.goodCode q (good C f)) (q*q) : ℤ) ∧
        Kept μ ν C.left) := by sorry
