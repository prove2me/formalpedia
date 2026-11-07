-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_columnContraction_le
-- name    : QEC.Coding.QuantumTanner.hammingWeight_columnContraction_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:50.901517+00:00
-- url     : https://prove2.me/theorems/bb8347d9-5125-469c-88df-6e7f2d0214e5
-- title:
--   Quantum Tanner: hamming Weight column Contraction le
-- statement:
--   Contraction cannot create a nonzero column where the original matrix is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L53-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L53-L66

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_columnContraction_le [DecidableEq F]
    (a : Word F A) (x : Word F (A × B)) :
    HammingWeight (columnContraction a x) ≤ HammingWeight x := by sorry
