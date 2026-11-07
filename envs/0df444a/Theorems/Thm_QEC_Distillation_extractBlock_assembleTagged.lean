-- Prove2me | Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
-- name    : QEC.Distillation.extractBlock_assembleTagged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:18.684205+00:00
-- url     : https://prove2.me/theorems/23335866-acb9-4ed6-89ec-8c8d2bbcb998
-- title:
--   Distillation: extract Block assemble Tagged
-- statement:
--   The Distillation construction uses the extract Block assemble Tagged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L75-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L75-L78

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]
omit [Field F] [Fintype F]

theorem QEC.Distillation.extractBlock_assembleTagged
    (blocks : ThreeCopyTag → ComputationalBasisRegisterLabel F ι) (tag : ThreeCopyTag) :
    extractBlock (assembleTagged blocks) tag = blocks tag := by sorry

attribute [defeq] QEC.Distillation.extractBlock_assembleTagged
