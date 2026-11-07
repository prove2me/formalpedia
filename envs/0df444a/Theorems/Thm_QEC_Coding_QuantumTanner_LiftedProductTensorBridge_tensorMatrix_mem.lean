-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTensorBridge_tensorMatrix_mem
-- name    : QEC.Coding.QuantumTanner.LiftedProductTensorBridge.tensorMatrix_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:34:41.282146+00:00
-- url     : https://prove2.me/theorems/30c0c920-fcf1-423d-863f-f01a08c1c569
-- title:
--   Lifted Product Tensor Bridge: tensor Matrix mem
-- statement:
--   Every matrix product satisfies the local tensor row and column constraints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean#L48-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean#L48-L65

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTensorBridge
open Classical
universe v
variable {A B C D : Type v} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductTensorBridge.tensorMatrix_mem (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2))
    (U : Matrix C D (ZMod 2)) :
    tensorMatrix P Q U ∈ (tensorCode (matrixRowCode P) (matrixRowCode Q)).carrier := by sorry
