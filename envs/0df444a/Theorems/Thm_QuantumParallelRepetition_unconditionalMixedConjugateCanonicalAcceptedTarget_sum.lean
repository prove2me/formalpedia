-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateCanonicalAcceptedTarget_sum
-- name    : QuantumParallelRepetition.unconditionalMixedConjugateCanonicalAcceptedTarget_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/8ad3fd1f-142a-4978-967c-981af12c3976
-- title:
--   QuantumParallelRepetition.unconditionalMixedConjugateCanonicalAcceptedTarget_sum
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

theorem QuantumParallelRepetition.unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Fin d) :
    (∑ i : Fin d, ∑ j : Fin d,
      (Real.sqrt (w * (d : ℝ)) : ℂ) *
        ((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
        (Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        dSVDensityRationalLocalSpectralPairBasisOverlap
          ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (a, b)) := by sorry
