-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_selected_retained_checks_orthogonal
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.selected_retained_checks_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:25:51.113676+00:00
-- url     : https://prove2.me/theorems/ad9f35f5-b6dd-4949-8d66-9b58c250f1d6
-- title:
--   Lifted Product Action Bridge: selected retained checks orthogonal
-- statement:
--   Actual selected checks commute after deleting the auxiliary coordinates.
--   Disjointness is derived from raw dual parity checks, not supplied as a bridge certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L275-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L275-L291

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.selected_retained_checks_orthogonal
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra (ZMod 2) G))
    (V0 V1 : Matrix C' D (MonoidAlgebra (ZMod 2) G)) :
    let U := zParameter (U0 * twistedMatrix gB (fun j => (b j)⁻¹)) (U1 * scalarMatrix gB)
    let V := xParameter ((scalarMatrix gA).transpose * V0)
      ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V1)
    (∑ j : B, ∑ i : A, ∑ g : G,
      zWord hA hB a b U (retainedCoordinate i j g) *
        xWord hA hB a b V (retainedCoordinate i j g)) = 0 := by sorry
