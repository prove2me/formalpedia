-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTensorBridge_mem_matrixRowCode
-- name    : QEC.Coding.QuantumTanner.LiftedProductTensorBridge.mem_matrixRowCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:30:28.186031+00:00
-- url     : https://prove2.me/theorems/d6272f31-608a-4183-9725-4ca0917c8e9f
-- title:
--   Lifted Product Tensor Bridge: mem matrix Row Code
-- statement:
--   Row membership is an actual finite coefficient combination of the rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean#L28-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean#L28-L40

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTensorBridge
open Classical
universe v
variable {A B C D : Type v} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductTensorBridge.mem_matrixRowCode (P : Matrix C A (ZMod 2)) (x : Word (ZMod 2) A) :
    x ∈ (matrixRowCode P).carrier ↔
      ∃ r : C → ZMod 2, ∀ i, (∑ c, r c * P c i) = x i := by sorry
