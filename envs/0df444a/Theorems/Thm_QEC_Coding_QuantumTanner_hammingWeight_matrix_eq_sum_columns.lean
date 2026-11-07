-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_matrix_eq_sum_columns
-- name    : QEC.Coding.QuantumTanner.hammingWeight_matrix_eq_sum_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:31:51.921188+00:00
-- url     : https://prove2.me/theorems/2bb361a3-6d01-4683-8815-df008d1ab771
-- title:
--   Quantum Tanner: hamming Weight matrix eq sum columns
-- statement:
--   Matrix weight is also the sum of the actual column weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L42-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L42-L47

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_matrix_eq_sum_columns (x : Word (ZMod 2) (A × B)) :
    HammingWeight x = ∑ b : B, HammingWeight (columnRestriction b x) := by sorry
