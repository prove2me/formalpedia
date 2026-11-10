-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_encodingLinearMap_apply_logical_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodingLinearMap_apply_logical_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:44.745676+00:00
-- url     : https://prove2.me/theorems/752effb2-5f39-420c-a7cd-2502b792f844
-- title:
--   Cubic Row Family: encoding Linear Map apply logical basis
-- statement:
--   On a logical computational ket the semantic encoder is the stated uniform coset ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1088-L1092
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1088-L1092

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodingLinearMap_apply_logical_basis (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    R.encodingLinearMap (registerBasisKet p u) = R.cosetKet u := by sorry
