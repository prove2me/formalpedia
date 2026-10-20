-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalClippedConjugateUnitTarget_distance_sq_le
-- name    : QuantumParallelRepetition.unconditionalClippedConjugateUnitTarget_distance_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/f1185f59-9449-4ad1-a9f1-81d79442210b
-- title:
--   QuantumParallelRepetition.unconditionalClippedConjugateUnitTarget_distance_sq_le
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

theorem QuantumParallelRepetition.unconditionalClippedConjugateUnitTarget_distance_sq_le
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖unconditionalConjugatePureVector psi -
      unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤
      2 * ‖psi - gamma.val‖ ^ 2 +
        8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by sorry
