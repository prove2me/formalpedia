-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalProjectorMatrix_eq
-- name    : QuantumParallelRepetition.dSVDensityRationalMixedCanonicalProjectorMatrix_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/eeaff9c8-c34f-4fc9-9a4c-dbae7101b98d
-- title:
--   QuantumParallelRepetition.dSVDensityRationalMixedCanonicalProjectorMatrix_eq
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

theorem QuantumParallelRepetition.dSVDensityRationalMixedCanonicalProjectorMatrix_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ := by sorry
