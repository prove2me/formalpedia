-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfConstantStrategy_outcomeProbability
-- name    : QuantumParallelRepetition.pdfConstantStrategy_outcomeProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/cb2d1dcd-3346-4387-8b7c-3962d4e126cc
-- title:
--   QuantumParallelRepetition.pdfConstantStrategy_outcomeProbability
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
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.pdfConstantStrategy_outcomeProbability
    (G : Game X Y A B) (a : A) (b : B)
    (x : X) (y : Y) (a' : A) (b' : B) :
    (pdfConstantStrategy G a b).outcomeProbability x y a' b' =
      if a' = a ∧ b' = b then 1 else 0 := by sorry
