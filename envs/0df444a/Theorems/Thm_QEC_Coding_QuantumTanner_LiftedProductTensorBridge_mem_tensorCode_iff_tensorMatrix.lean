-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTensorBridge_mem_tensorCode_iff_tensorMatrix
-- name    : QEC.Coding.QuantumTanner.LiftedProductTensorBridge.mem_tensorCode_iff_tensorMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:02:44.633234+00:00
-- url     : https://prove2.me/theorems/17b1e816-fc79-489d-9e59-9a550380b4d6
-- title:
--   Lifted Product Tensor Bridge: mem tensor Code iff tensor Matrix
-- statement:
--   Both tensor-code constraints are sufficient for an actual matrix-product parameter.
--   The proof uses tensor-code induction on pure products of local row-code words.
--   No global bridge equality or factorization certificate is an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean#L70-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean#L70-L95

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTensorBridge
open Classical
universe v
variable {A B C D : Type v} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductTensorBridge.mem_tensorCode_iff_tensorMatrix
    (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2)) (x : Word (ZMod 2) (A × B)) :
    x ∈ (tensorCode (matrixRowCode P) (matrixRowCode Q)).carrier ↔
      ∃ U : Matrix C D (ZMod 2), tensorMatrix P Q U = x := by sorry
