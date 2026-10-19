-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfGreedyCard_lt_of_ceil
-- name    : QuantumParallelRepetition.pdfGreedyCard_lt_of_ceil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/abcad539-f344-4759-968c-b72d37b1aa28
-- title:
--   QuantumParallelRepetition.pdfGreedyCard_lt_of_ceil
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.pdfGreedyCard_lt_of_ceil
    (k n : ℕ) (τ d : ℝ)
    (below : k < ⌈d * (n : ℝ) / τ⌉₊) :
    (k : ℝ) < d * (n : ℝ) / τ := by sorry
