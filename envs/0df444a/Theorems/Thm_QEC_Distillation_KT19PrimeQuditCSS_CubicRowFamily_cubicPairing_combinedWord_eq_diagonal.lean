-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicPairing_combinedWord_eq_diagonal
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicPairing_combinedWord_eq_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:39.245582+00:00
-- url     : https://prove2.me/theorems/cd3c5e4e-ce53-4cbe-9de5-0a2f2478ec4e
-- title:
--   Cubic Row Family: cubic Pairing combined Word eq diagonal
-- statement:
--   Strong row orthogonality reduces every cubic row combination to its diagonal logical terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L817-L878
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L817-L878

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicPairing_combinedWord_eq_diagonal (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → ZMod p) :
    cubicPairing p (R.combinedWord q) (R.combinedWord q) (R.combinedWord q) =
      ∑ a : Logical, q (Sum.inl a) ^ 3 * R.epsilon a := by sorry
