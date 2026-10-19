-- Prove2me | Theorems.Thm_QuantumParallelRepetition_residualIdentity_quadratic
-- name    : QuantumParallelRepetition.residualIdentity_quadratic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/dab7d200-83b6-41f6-847f-f4783d657d2c
-- title:
--   QuantumParallelRepetition.residualIdentity_quadratic
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
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.residualIdentity_quadratic
    {s t : Type} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (M : Matrix s s ℂ)
    (z : EuclideanSpace ℂ s)
    (κ : EuclideanSpace ℂ t)
    (normalized : ‖κ‖ = 1) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (M ⊗ₖ (1 : Matrix t t ℂ)))
      (toLp 2 (fun q : s × t => z q.1 * κ q.2)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) M) z := by sorry
