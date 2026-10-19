-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
-- name    : QuantumParallelRepetition.dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/bf1dda52-bd70-4fae-87ea-d1b0d3246036
-- title:
--   QuantumParallelRepetition.dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
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
open scoped BigOperators ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d)
    (i : Fin d) (k : Fin N) :
    dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ↔
      k.val <
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val := by sorry
