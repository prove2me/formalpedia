-- Prove2me | Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_injective
-- name    : QuantumParallelRepetition.matrixQuadraticExpectation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/06b5d818-5806-4b42-b29d-11c27cd846d3
-- title:
--   QuantumParallelRepetition.matrixQuadraticExpectation_injective
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

theorem QuantumParallelRepetition.matrixQuadraticExpectation_injective
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (f : d → e) (injective : Function.Injective f)
    (M : Matrix e e ℂ) (N : Matrix d d ℂ)
    (v : EuclideanSpace ℂ e) (z : EuclideanSpace ℂ d)
    (included : ∀ i : d, v (f i) = z i)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → v j = 0)
    (compressed : ∀ i j : d, M (f i) (f j) = N i j) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) M) v =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) N) z := by sorry
