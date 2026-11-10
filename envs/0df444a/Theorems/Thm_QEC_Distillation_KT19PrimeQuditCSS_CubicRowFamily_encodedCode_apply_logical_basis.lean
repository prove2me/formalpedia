-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_encodedCode_apply_logical_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodedCode_apply_logical_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:44:09.857943+00:00
-- url     : https://prove2.me/theorems/a46be0e2-7a8c-407e-bc61-1531f5d73e7e
-- title:
--   Cubic Row Family: encoded Code apply logical basis
-- statement:
--   The encoded code exposes the same ambient vector on a logical basis ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1095-L1098
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1095-L1098

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodedCode_apply_logical_basis (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    R.encodedCode.encode (registerBasisKet p u) = R.cosetKet u := by sorry
