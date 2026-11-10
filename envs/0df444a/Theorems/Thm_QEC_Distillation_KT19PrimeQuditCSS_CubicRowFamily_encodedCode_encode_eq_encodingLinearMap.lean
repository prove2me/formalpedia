-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_encodedCode_encode_eq_encodingLinearMap
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodedCode_encode_eq_encodingLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:44:15.729067+00:00
-- url     : https://prove2.me/theorems/4f837b66-78ac-400b-b698-677c89b96e07
-- title:
--   Cubic Row Family: encoded Code encode eq encoding Linear Map
-- statement:
--   The semantic encoded code has the concrete normalized-coset linear map as its encoder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1101-L1104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1101-L1104

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
open QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_633
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_634
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_635

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodedCode_encode_eq_encodingLinearMap (R : CubicRowFamily p Logical Stabilizer Site)
    (psi : PrimeQuditRegister p Logical) :
    R.encodedCode.encode psi = R.encodingLinearMap psi := by sorry
