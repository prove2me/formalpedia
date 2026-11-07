-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_zWord_auxiliary_eq
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.zWord_auxiliary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:30.41794+00:00
-- url     : https://prove2.me/theorems/dddf5257-e17c-4453-9d17-160f2e3b185b
-- title:
--   Lifted Product Action Bridge: z Word auxiliary eq
-- statement:
--   Coefficientwise identification of actual Z auxiliaries with the ordered source blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L181-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L181-L192

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductActionBridge
open QEC.Coding.LiftedProduct
open QEC.Coding.QuantumTanner.LiftedProductRestriction
noncomputable section
variable {G A B C D : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.zWord_auxiliary_eq (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    zWord hA hB a b (zParameter U0 U1) (auxiliaryCoordinate c d g) =
      (zAuxiliary (scalarMatrix hB) (twistedMatrix hB b) U0 U1 c d).coeff g := by sorry
