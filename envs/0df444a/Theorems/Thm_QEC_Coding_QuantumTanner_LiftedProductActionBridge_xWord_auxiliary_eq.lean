-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_xWord_auxiliary_eq
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.xWord_auxiliary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:29.531209+00:00
-- url     : https://prove2.me/theorems/b294e2af-4f5c-425f-b27f-1d771f8b19c3
-- title:
--   Lifted Product Action Bridge: x Word auxiliary eq
-- statement:
--   Coefficientwise identification of actual X auxiliaries with the ordered source blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L195-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L195-L206

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.xWord_auxiliary_eq (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    xWord hA hB a b (xParameter V0 V1) (auxiliaryCoordinate c d g) =
      (xAuxiliary (scalarMatrix hA) (twistedMatrix hA a) V0 V1 c d).coeff g := by sorry
