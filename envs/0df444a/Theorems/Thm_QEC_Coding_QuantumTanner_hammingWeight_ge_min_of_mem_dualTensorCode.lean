-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_ge_min_of_mem_dualTensorCode
-- name    : QEC.Coding.QuantumTanner.hammingWeight_ge_min_of_mem_dualTensorCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:14:18.240254+00:00
-- url     : https://prove2.me/theorems/b42772e0-76b2-454c-81a8-ebe15a4f4310
-- title:
--   Quantum Tanner: hamming Weight ge min of mem dual Tensor Code
-- statement:
--   Every nonzero word of the actual row/column sum has weight at least the
--   minimum of the two local distance lower bounds. No nonemptiness is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L84-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L84-L116

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_ge_min_of_mem_dualTensorCode [DecidableEq F]
    (CA : LinearCode F A) (CB : LinearCode F B) (dA dB : Nat)
    (hA : ∀ a : Word F A, a ∈ CA.carrier → a ≠ 0 → dA ≤ HammingWeight a)
    (hB : ∀ b : Word F B, b ∈ CB.carrier → b ≠ 0 → dB ≤ HammingWeight b)
    (x : Word F (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier) (hne : x ≠ 0) :
    min dA dB ≤ HammingWeight x := by sorry
