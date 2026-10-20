-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateCanonicalAcceptedTarget_apply
-- name    : QuantumParallelRepetition.unconditionalConjugateCanonicalAcceptedTarget_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/411cd812-fde0-48c8-9acf-0a07d539a362
-- title:
--   QuantumParallelRepetition.unconditionalConjugateCanonicalAcceptedTarget_apply
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

theorem QuantumParallelRepetition.unconditionalConjugateCanonicalAcceptedTarget_apply
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (a b : Fin d) :
    star
        (dSVDensityRationalCanonicalAcceptedTarget w N ξ
          (a, b)) =
      ∑ i : Fin d,
        (dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) b i) := by sorry
