-- Prove2me | Theorems.Thm_QuantumParallelRepetition_divisor_greedy_card_mul_lt
-- name    : QuantumParallelRepetition.divisor_greedy_card_mul_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/a9b838ca-51f4-4b8e-b203-aed0a7f711b1
-- title:
--   QuantumParallelRepetition.divisor_greedy_card_mul_lt
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.divisor_greedy_card_mul_lt
    {n q : ℕ} (hq : 0 < q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    D.card * q < n := by sorry
