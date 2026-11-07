-- Prove2me | Theorems.Thm_QEC_Distillation_threeWordTransport_basis
-- name    : QEC.Distillation.threeWordTransport_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:52:23.585883+00:00
-- url     : https://prove2.me/theorems/11d885e2-32f8-404f-8ccd-21bba335b7eb
-- title:
--   Distillation: three Word Transport basis
-- statement:
--   The Distillation construction uses the three Word Transport basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L71-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L71-L74

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

theorem QEC.Distillation.threeWordTransport_basis (a : (J → F) × (J → F) × (J → F)) :
    threeWordTransport F J (EuclideanSpace.basisFun _ Complex a) =
      EuclideanSpace.basisFun _ Complex (threeWordEquiv F J a) := by sorry
