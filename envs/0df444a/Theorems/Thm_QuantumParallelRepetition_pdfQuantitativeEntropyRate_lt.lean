-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfQuantitativeEntropyRate_lt
-- name    : QuantumParallelRepetition.pdfQuantitativeEntropyRate_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/170acf0e-2711-4ab5-a0f1-f852a3950fba
-- title:
--   QuantumParallelRepetition.pdfQuantitativeEntropyRate_lt
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

theorem QuantumParallelRepetition.pdfQuantitativeEntropyRate_lt
    {n m k : ℕ} {t d τ ell : ℝ}
    (length : 0 < n) (rate : 0 < d) (tolerance : 0 < τ)
    (alphabet : 0 ≤ ell)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection : t < d * (n : ℝ))
    (conditioned : (k : ℝ) < d * (n : ℝ) / τ) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      2 * d * (1 + ell / τ) := by sorry
