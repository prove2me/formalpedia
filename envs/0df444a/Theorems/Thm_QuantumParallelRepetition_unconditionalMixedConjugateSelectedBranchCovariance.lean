-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranchCovariance
-- name    : QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranchCovariance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/0ffc9a91-1b8d-4b25-91bb-2b422e838cab
-- title:
--   QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranchCovariance
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

theorem QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranchCovariance
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (rest : EuclideanSpace ℂ τ) :
    Real.sqrt (width (schedule j) * (d : ℝ)) •
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis ξ)))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ζ)))
        (unconditionalSelectedCopyIdealMatchedBranch
          (N := N) (B := B) (m := m)
          width schedule ξ ζ j rest) =
      unconditionalMatchedVerifierTensor
        (unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
          (N := N) (B := B) (width (schedule j)) m ξ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j rest) := by sorry
