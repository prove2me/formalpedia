-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
-- name    : QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/8e8c12ad-42a3-4894-810c-dca1c05ebe4a
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
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

theorem QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * ((dSVDensityRationalPhysicalAcceptedRank
        w N ξ i).val : ℝ) / (N : ℝ) := by sorry
