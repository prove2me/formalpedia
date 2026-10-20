-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exists_source_rounding_divisor
-- name    : QuantumParallelRepetition.exists_source_rounding_divisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/d47dd20a-c714-4dc2-8b12-5efc4768ef80
-- title:
--   QuantumParallelRepetition.exists_source_rounding_divisor
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

theorem QuantumParallelRepetition.exists_source_rounding_divisor
    (A B : Type*) [Fintype A] [Fintype B]
    {K η δ : ℝ}
    (hK : 0 ≤ K) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧
      8 * K *
          ((2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
            (q : ℝ)) ≤
        δ ^ 2 := by sorry
