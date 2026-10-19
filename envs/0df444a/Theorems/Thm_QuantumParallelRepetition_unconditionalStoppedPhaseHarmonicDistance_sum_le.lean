-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalStoppedPhaseHarmonicDistance_sum_le
-- name    : QuantumParallelRepetition.unconditionalStoppedPhaseHarmonicDistance_sum_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/71d25597-f3c9-44ce-96ad-06b24669a486
-- title:
--   QuantumParallelRepetition.unconditionalStoppedPhaseHarmonicDistance_sum_le
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

theorem QuantumParallelRepetition.unconditionalStoppedPhaseHarmonicDistance_sum_le
    {J K : Type*} [Fintype K]
    {d B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : J → EuclideanSpace ℂ (Fin d × Fin d))
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1)
    (j : J) :
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (x j) (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (y j) (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      ‖x j - y j‖ ^ 2 := by sorry
