-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfEntropyRoundingLoss_lt_gapQuarter
-- name    : QuantumParallelRepetition.pdfEntropyRoundingLoss_lt_gapQuarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/03c6faed-7274-4ea5-99d5-9ef17525b1d6
-- title:
--   QuantumParallelRepetition.pdfEntropyRoundingLoss_lt_gapQuarter
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

theorem QuantumParallelRepetition.pdfEntropyRoundingLoss_lt_gapQuarter
    {B ε η : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (entropy : 0 ≤ η)
    (small : η < (ε / (4 * B)) ^ (12 : ℕ)) :
    B * η ^ (1 / 12 : ℝ) < ε / 4 := by sorry
