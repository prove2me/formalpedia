-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
-- name    : QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/9c4bd3b2-8d51-4037-a7d4-c00b545e5ecb
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
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

theorem QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix.blockDiagonal'
        (dSVDensityRationalPhysicalProjector w ξ) =
      (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalCanonicalPrefixMask w N ξ *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by sorry
