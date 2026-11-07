-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerCode_quantumTanner_from_liftedProduct
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerCode.quantumTanner_from_liftedProduct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:37:47.397796+00:00
-- url     : https://prove2.me/theorems/6114bc67-89c9-44be-940b-82ece6a465d9
-- title:
--   Lifted Product Tanner Code: quantum Tanner from lifted Product
-- statement:
--   The selected, punctured canonical lifted product has exactly the two
--   check spaces of the explicitly constructed public Quantum Tanner data.
--   The lift and the Tanner data are outputs constructed from the scalar input;
--   neither is an arbitrary code nor a conclusion-bearing certificate premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerCode.lean#L281-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerCode.lean#L281-L327

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerCode
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerCode
open Classical LiftedProductTannerBridge LiftedProductTensorBridge
open LiftedProductActionBridge LiftedProductRestriction
variable {G A B : Type} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {C D C' D' : Type} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']

theorem QEC.Coding.QuantumTanner.LiftedProductTannerCode.quantumTanner_from_liftedProduct
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (bridgeLeft : A → G) (bridgeRight : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, bridgeLeft (invA i) = (bridgeLeft i)⁻¹) (hInvB : ∀ j, bridgeRight (invB j) = (bridgeRight j)⁻¹)
    (hDualA : _root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA) =
      (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : _root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gB) =
      (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let lifted : _root_.QEC.Coding.LiftedProduct.Data (ZMod 2) G (Bool × D) B A (Bool × C) :=
      LiftedProductActionBridge.canonicalData hA hB bridgeLeft bridgeRight
    let tanner : _root_.QEC.Coding.QuantumTanner.Data (VertexGroup G) A B (A × B × G)
        (Fin (Dimension (tensorCode (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA)).dual
          (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB)).dual)))
        (Fin (Dimension (tensorCode (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
          (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))))) :=
      selectedData hA hB gA gB bridgeLeft bridgeRight invA invB hInvA hInvB hDualA hDualB
    Set.range (fun U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
        Matrix C D' (MonoidAlgebra (ZMod 2) G) => fun (i, j, g) =>
      (LiftedProduct.boundary2Matrix lifted).mulVec
        (zParameter (U.1 * twistedMatrix gB (fun j => (bridgeRight j)⁻¹)) (U.2 * scalarMatrix gB))
        (retainedCoordinate i j g)) = (LinearMap.range tanner.toRawData.zGeneratorMap).carrier ∧
    Set.range (fun V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
        Matrix C' D (MonoidAlgebra (ZMod 2) G) => fun (i, j, g) =>
      (LiftedProduct.boundary1Matrix lifted).transpose.mulVec
        (xParameter ((scalarMatrix gA).transpose * V.1)
          ((twistedMatrix gA (fun i => (bridgeLeft i)⁻¹)).transpose * V.2))
        (retainedCoordinate i j g)) = (LinearMap.range tanner.toRawData.xGeneratorMap).carrier ∧
    tanner.blockLength = Fintype.card G * Fintype.card A * Fintype.card B := by sorry
