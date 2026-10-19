-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalCanonicalAcceptedCoefficient_sourceScale
-- name    : QuantumParallelRepetition.unconditionalCanonicalAcceptedCoefficient_sourceScale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/6a80128f-10e8-462b-972c-403bb64618a7
-- title:
--   QuantumParallelRepetition.unconditionalCanonicalAcceptedCoefficient_sourceScale
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

theorem QuantumParallelRepetition.unconditionalCanonicalAcceptedCoefficient_sourceScale
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) =
      dSVDensityRationalCanonicalAcceptedCoefficient w N ξ i := by sorry
