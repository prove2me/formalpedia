-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
-- name    : QEC.Distillation.taggedCczTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:22.191504+00:00
-- url     : https://prove2.me/theorems/1981de5c-f5e5-40d3-b3e9-68e78b819bd1
-- title:
--   Distillation: tagged Ccz Transport apply
-- statement:
--   The Distillation construction uses the tagged Ccz Transport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L319-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L319-L323

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

theorem QEC.Distillation.taggedCczTransport_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczTransport site psi label = taggedCczAmplitude site label * psi label := by sorry

attribute [defeq] QEC.Distillation.taggedCczTransport_apply
