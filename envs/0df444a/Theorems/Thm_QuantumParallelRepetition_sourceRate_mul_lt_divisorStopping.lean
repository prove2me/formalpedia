-- Prove2me | Theorems.Thm_QuantumParallelRepetition_sourceRate_mul_lt_divisorStopping
-- name    : QuantumParallelRepetition.sourceRate_mul_lt_divisorStopping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/0e582fa0-1491-469c-aabc-d5c2b46b3637
-- title:
--   QuantumParallelRepetition.sourceRate_mul_lt_divisorStopping
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

theorem QuantumParallelRepetition.sourceRate_mul_lt_divisorStopping
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n)
    {η : ℝ} (hη : 0 < η) :
    (η / (4 * (q : ℝ))) * (n : ℝ) <
      η * ((n / q : ℕ) : ℝ) := by sorry
