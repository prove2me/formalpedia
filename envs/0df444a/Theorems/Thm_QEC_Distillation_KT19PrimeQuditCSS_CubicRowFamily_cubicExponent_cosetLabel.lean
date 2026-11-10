-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicExponent_cosetLabel
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicExponent_cosetLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:23.175854+00:00
-- url     : https://prove2.me/theorems/1b25de9c-5606-418b-9a27-e20e0ba37e2c
-- title:
--   Cubic Row Family: cubic Exponent coset Label
-- statement:
--   The cubic exponent of every CSS coset label is the negative logical diagonal form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L881-L895
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L881-L895

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicExponent_cosetLabel (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    cubicExponent p (R.cosetLabel u h) =
      -(∑ a : Logical, u a ^ 3 * R.epsilon a) := by sorry
