-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
-- name    : QEC.Distillation.taggedCczLinearEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:04.525062+00:00
-- url     : https://prove2.me/theorems/67d83b83-59f2-4c99-a832-c0b6d1a90994
-- title:
--   Distillation: tagged Ccz Linear Equiv symm apply
-- statement:
--   The Distillation construction uses the tagged Ccz Linear Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L305-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L305-L310

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]

theorem QEC.Distillation.taggedCczLinearEquiv_symm_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    (taggedCczLinearEquiv (F := F) site).symm psi label =
      taggedCczAmplitude site label * psi label := by sorry

attribute [defeq] QEC.Distillation.taggedCczLinearEquiv_symm_apply
