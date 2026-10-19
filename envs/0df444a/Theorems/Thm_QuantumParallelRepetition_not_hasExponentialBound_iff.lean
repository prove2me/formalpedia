-- Prove2me | Theorems.Thm_QuantumParallelRepetition_not_hasExponentialBound_iff
-- name    : QuantumParallelRepetition.not_hasExponentialBound_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/ab6cf790-d7d6-4b76-aa71-f3fb3ab1efad
-- title:
--   QuantumParallelRepetition.not_hasExponentialBound_iff
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

theorem QuantumParallelRepetition.not_hasExponentialBound_iff (v : ℕ → ℝ) :
    ¬ HasExponentialBound v ↔ HasSubexponentialWitness v := by sorry
