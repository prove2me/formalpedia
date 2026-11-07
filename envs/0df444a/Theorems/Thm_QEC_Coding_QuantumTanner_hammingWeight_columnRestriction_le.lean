-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_columnRestriction_le
-- name    : QEC.Coding.QuantumTanner.hammingWeight_columnRestriction_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:53.562194+00:00
-- url     : https://prove2.me/theorems/b3bac65c-8275-438a-b091-5a1ba023e0f6
-- title:
--   Quantum Tanner: hamming Weight column Restriction le
-- statement:
--   A single column has no more nonzero coordinates than the full matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L69-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L69-L80

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_columnRestriction_le [DecidableEq F]
    (b : B) (x : Word F (A × B)) :
    HammingWeight (columnRestriction b x) ≤ HammingWeight x := by sorry
