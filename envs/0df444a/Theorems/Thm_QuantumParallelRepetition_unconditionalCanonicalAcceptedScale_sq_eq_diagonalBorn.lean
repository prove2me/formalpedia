-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
-- name    : QuantumParallelRepetition.unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/dc707594-af43-45fc-9dd4-d436b7046b98
-- title:
--   QuantumParallelRepetition.unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
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

theorem QuantumParallelRepetition.unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (gamma : BipartiteUnitVector d) :
    (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ / Real.sqrt (w * (d : ℝ))) ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w gamma := by sorry
