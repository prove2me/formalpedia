-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_selected_words_auxiliary_disjoint
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.selected_words_auxiliary_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:33.547913+00:00
-- url     : https://prove2.me/theorems/dbde0f24-529e-485a-a18e-67f70f8cc5ae
-- title:
--   Lifted Product Action Bridge: selected words auxiliary disjoint
-- statement:
--   The selected actual boundary supports are disjoint on every auxiliary qubit.
--   Only the two raw scalar dual-check equations are assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L212-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L212-L231

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
variable {C' D' : Type*} [Fintype C'] [Fintype D']

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.selected_words_auxiliary_disjoint
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra (ZMod 2) G))
    (V0 V1 : Matrix C' D (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    zWord hA hB a b
        (zParameter (U0 * twistedMatrix gB (fun j => (b j)⁻¹)) (U1 * scalarMatrix gB))
        (auxiliaryCoordinate c d g) = 0 ∨
      xWord hA hB a b
        (xParameter ((scalarMatrix gA).transpose * V0)
          ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V1))
        (auxiliaryCoordinate c d g) = 0 := by sorry
