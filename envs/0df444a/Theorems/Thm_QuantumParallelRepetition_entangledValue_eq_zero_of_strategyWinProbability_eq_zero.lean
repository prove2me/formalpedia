-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_eq_zero_of_strategyWinProbability_eq_zero
-- name    : QuantumParallelRepetition.entangledValue_eq_zero_of_strategyWinProbability_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/7cb78bc8-7bdb-4b18-9b50-3eb5d4c905ec
-- title:
--   QuantumParallelRepetition.entangledValue_eq_zero_of_strategyWinProbability_eq_zero
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

theorem QuantumParallelRepetition.entangledValue_eq_zero_of_strategyWinProbability_eq_zero
    (G : Game X Y A B)
    (hzero : ∀ S : Strategy G, S.winProbability = 0) :
    entangledValue G = 0 := by sorry
