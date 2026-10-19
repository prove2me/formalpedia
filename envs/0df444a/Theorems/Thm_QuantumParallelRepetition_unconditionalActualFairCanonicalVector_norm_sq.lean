-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCanonicalVector_norm_sq
-- name    : QuantumParallelRepetition.unconditionalActualFairCanonicalVector_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/71254d5b-0d86-4feb-9129-e3a36f72747d
-- title:
--   QuantumParallelRepetition.unconditionalActualFairCanonicalVector_norm_sq
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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairCanonicalVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by sorry
