-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensor_approximation_of_robust
-- name    : QEC.Coding.QuantumTanner.exists_tensor_approximation_of_robust
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:56:51.755546+00:00
-- url     : https://prove2.me/theorems/5788d5e4-e353-46cf-ab3c-4cda5b865558
-- title:
--   Quantum Tanner: exists tensor approximation of robust
-- statement:
--   Any close column- and row-code witnesses yield an actual tensor word at
--   distance at most `3/2` times the sum of their residual weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorApproximation.lean#L53-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorApproximation.lean#L53-L100

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorApproximation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_tensor_approximation_of_robust
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hBudget : 2 * w ≤ dA * dB)
    (x C R : Word (ZMod 2) (A × B))
    (hC : C ∈ (columnCode (B := B) CA).carrier)
    (hR : R ∈ (rowCode (A := A) CB).carrier)
    (hClose : HammingWeight (x + C) + HammingWeight (x + R) ≤ w) :
    ∃ z : Word (ZMod 2) (A × B), z ∈ (tensorCode CA CB).carrier ∧
      2 * HammingWeight (x + z) ≤
        3 * (HammingWeight (x + C) + HammingWeight (x + R)) := by sorry
