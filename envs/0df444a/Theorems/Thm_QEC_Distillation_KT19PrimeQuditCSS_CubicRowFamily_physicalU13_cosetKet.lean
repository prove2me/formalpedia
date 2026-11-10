-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_cosetKet
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_cosetKet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:43:03.217977+00:00
-- url     : https://prove2.me/theorems/165d39eb-5f01-4901-bfc5-791ef8284121
-- title:
--   Cubic Row Family: physical U13 coset Ket
-- statement:
--   The physical cubic product gives the specified inverse logical phase on each coset ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1139-L1153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1139-L1153

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_cosetKet (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p (R.cosetKet u) = R.logicalInverseAmplitude u • R.cosetKet u := by sorry
