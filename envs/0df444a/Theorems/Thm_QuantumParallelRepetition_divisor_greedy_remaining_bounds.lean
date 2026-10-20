-- Prove2me | Theorems.Thm_QuantumParallelRepetition_divisor_greedy_remaining_bounds
-- name    : QuantumParallelRepetition.divisor_greedy_remaining_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/0639a9c3-e17c-47af-b946-54bfedb7dd78
-- title:
--   QuantumParallelRepetition.divisor_greedy_remaining_bounds
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
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.divisor_greedy_remaining_bounds
    {n q : ℕ} (hq : 2 ≤ q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    0 < (Finset.univ \ D).card ∧
      n ≤ 2 * (Finset.univ \ D).card ∧
      D.card * q ≤ 2 * (Finset.univ \ D).card := by sorry
