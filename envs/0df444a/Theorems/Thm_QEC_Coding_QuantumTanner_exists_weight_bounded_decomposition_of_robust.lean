-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_weight_bounded_decomposition_of_robust
-- name    : QEC.Coding.QuantumTanner.exists_weight_bounded_decomposition_of_robust
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:55:41.953928+00:00
-- url     : https://prove2.me/theorems/8c4c09bf-56b9-497b-aec6-8afde7c994e3
-- title:
--   Quantum Tanner: exists weight bounded decomposition of robust
-- statement:
--   Robustness below the half-product-distance budget yields an attained
--   row/column decomposition whose parts have no more weight than their sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorApproximation.lean#L23-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorApproximation.lean#L23-L49

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorApproximation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_weight_bounded_decomposition_of_robust
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hBudget : 2 * w ≤ dA * dB)
    (y : Word (ZMod 2) (A × B))
    (hy : y ∈ (dualTensorCode CA CB).carrier) (hWeight : HammingWeight y ≤ w) :
    ∃ r c : Word (ZMod 2) (A × B),
      r ∈ (rowCode (A := A) CB).carrier ∧
      c ∈ (columnCode (B := B) CA).carrier ∧
      y = r + c ∧ HammingWeight r ≤ HammingWeight y ∧
        HammingWeight c ≤ HammingWeight y := by sorry
