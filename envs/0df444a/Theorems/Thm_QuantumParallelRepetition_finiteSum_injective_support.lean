-- Prove2me | Theorems.Thm_QuantumParallelRepetition_finiteSum_injective_support
-- name    : QuantumParallelRepetition.finiteSum_injective_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/52ee56ff-405c-448c-813e-7578ef9df7a2
-- title:
--   QuantumParallelRepetition.finiteSum_injective_support
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.finiteSum_injective_support
    {d e K : Type*} [Fintype d] [Fintype e] [AddCommMonoid K]
    (f : d → e) (injective : Function.Injective f)
    (g : e → K)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → g j = 0) :
    (∑ j : e, g j) = ∑ i : d, g (f i) := by sorry
