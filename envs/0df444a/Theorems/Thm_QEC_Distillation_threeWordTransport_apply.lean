-- Prove2me | Theorems.Thm_QEC_Distillation_threeWordTransport_apply
-- name    : QEC.Distillation.threeWordTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:55.546992+00:00
-- url     : https://prove2.me/theorems/8cea1853-3b52-4f32-b91c-1faf627033bd
-- title:
--   Distillation: three Word Transport apply
-- statement:
--   The Distillation construction uses the three Word Transport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L76-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L76-L85

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

theorem QEC.Distillation.threeWordTransport_apply
    (psi : EuclideanSpace Complex ((J → F) × (J → F) × (J → F)))
    (a : (J → F) × (J → F) × (J → F)) :
    threeWordTransport F J psi (threeWordEquiv F J a) = psi a := by sorry
