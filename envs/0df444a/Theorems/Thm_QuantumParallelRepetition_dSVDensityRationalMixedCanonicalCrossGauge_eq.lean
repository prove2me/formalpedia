-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalCrossGauge_eq
-- name    : QuantumParallelRepetition.dSVDensityRationalMixedCanonicalCrossGauge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/e91af8ab-000d-428b-bd09-2aeb6bdb314c
-- title:
--   QuantumParallelRepetition.dSVDensityRationalMixedCanonicalCrossGauge_eq
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

theorem QuantumParallelRepetition.dSVDensityRationalMixedCanonicalCrossGauge_eq
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) =
      dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ := by sorry
