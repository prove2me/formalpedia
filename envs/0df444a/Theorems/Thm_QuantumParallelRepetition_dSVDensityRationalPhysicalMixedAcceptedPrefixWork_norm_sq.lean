-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
-- name    : QuantumParallelRepetition.dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/f2c50c58-6705-4441-81b5-a08fd51c0f72
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    ‖dSVDensityRationalPhysicalMixedAcceptedPrefixWork
        w N ξ ζ i j‖ ^ 2 =
      ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val : ℝ) := by sorry
