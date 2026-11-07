-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_columnContraction_mem_of_mem_dualTensorCode
-- name    : QEC.Coding.QuantumTanner.columnContraction_mem_of_mem_dualTensorCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:35.679079+00:00
-- url     : https://prove2.me/theorems/e45eab09-ba62-4e28-bbf1-d62546b67f78
-- title:
--   Quantum Tanner: column Contraction mem of mem dual Tensor Code
-- statement:
--   Contracting a dual-tensor word by a dual `C_A` word gives a `C_B` word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L38-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L38-L50

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.columnContraction_mem_of_mem_dualTensorCode
    (CA : LinearCode F A) (CB : LinearCode F B) (a : Word F A)
    (ha : a ∈ CA.dual.carrier) (x : Word F (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) :
    columnContraction a x ∈ CB.carrier := by sorry
