-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicPairing_combinedWord
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicPairing_combinedWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:21.234556+00:00
-- url     : https://prove2.me/theorems/786aedab-c4d7-4046-b5b9-c44e473b8b1a
-- title:
--   Cubic Row Family: cubic Pairing combined Word
-- statement:
--   Expanding a cubic pairing of arbitrary finite row combinations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L703-L780
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L703-L780

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

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicPairing_combinedWord (R : CubicRowFamily p Logical Stabilizer Site)
    (q r s : Logical ⊕ Stabilizer → ZMod p) :
    cubicPairing p (R.combinedWord q) (R.combinedWord r) (R.combinedWord s) =
      ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, q a * r b * s c * cubicPairing p (R.row a) (R.row b) (R.row c) := by sorry
