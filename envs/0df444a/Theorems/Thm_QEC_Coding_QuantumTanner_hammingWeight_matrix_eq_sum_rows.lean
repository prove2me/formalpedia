-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_matrix_eq_sum_rows
-- name    : QEC.Coding.QuantumTanner.hammingWeight_matrix_eq_sum_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:31:39.703274+00:00
-- url     : https://prove2.me/theorems/8bd4542f-d6b4-4877-8e40-49c6937bc253
-- title:
--   Quantum Tanner: hamming Weight matrix eq sum rows
-- statement:
--   Matrix weight is the sum of the actual row weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L35-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L35-L39

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_matrix_eq_sum_rows (x : Word (ZMod 2) (A × B)) :
    HammingWeight x = ∑ a : A, HammingWeight (rowRestriction a x) := by sorry
