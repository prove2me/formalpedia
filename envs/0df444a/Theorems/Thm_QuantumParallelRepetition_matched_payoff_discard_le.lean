-- Prove2me | Theorems.Thm_QuantumParallelRepetition_matched_payoff_discard_le
-- name    : QuantumParallelRepetition.matched_payoff_discard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/1b1ceac8-f362-4a14-907a-973dbcb1acd8
-- title:
--   QuantumParallelRepetition.matched_payoff_discard_le
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.matched_payoff_discard_le
    {ι : Type*} [Fintype ι]
    (weight payoff : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (payoff_le_one : ∀ i, payoff i ≤ 1)
    (matched : ι → Bool) :
    (∑ i, weight i * payoff i) -
        (∑ i, weight i * if matched i then 0 else 1) ≤
      ∑ i, weight i * if matched i then payoff i else 0 := by sorry
