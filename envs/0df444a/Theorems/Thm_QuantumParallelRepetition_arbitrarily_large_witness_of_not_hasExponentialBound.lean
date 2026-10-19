-- Prove2me | Theorems.Thm_QuantumParallelRepetition_arbitrarily_large_witness_of_not_hasExponentialBound
-- name    : QuantumParallelRepetition.arbitrarily_large_witness_of_not_hasExponentialBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/544639cb-f2be-46e3-b943-e75260c7187f
-- title:
--   QuantumParallelRepetition.arbitrarily_large_witness_of_not_hasExponentialBound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators

theorem QuantumParallelRepetition.arbitrarily_large_witness_of_not_hasExponentialBound
    {v : ℕ → ℝ}
    (hv : ∀ n : ℕ, v n ≤ 1)
    (h_no_bound : ¬ HasExponentialBound v)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Real.exp (-c * (n : ℝ)) < v n := by sorry
