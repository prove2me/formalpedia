-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_intertwines_encodingLinearMap
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_intertwines_encodingLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:39.484047+00:00
-- url     : https://prove2.me/theorems/65562472-0974-4720-a737-2bd97ac86c6a
-- title:
--   Cubic Row Family: physical U13 intertwines encoding Linear Map
-- statement:
--   Full pointwise encoder-commuting equation for the physical and inverse logical cubic gates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1156-L1170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1156-L1170

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_intertwines_encodingLinearMap (R : CubicRowFamily p Logical Stabilizer Site)
    (psi : PrimeQuditRegister p Logical) :
    _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p (R.encodingLinearMap psi) =
    R.encodingLinearMap (R.logicalInverseU13 psi)
    := by sorry
