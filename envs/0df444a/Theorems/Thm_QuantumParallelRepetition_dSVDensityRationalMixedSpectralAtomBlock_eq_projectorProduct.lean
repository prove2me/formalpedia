-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
-- name    : QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/e5cd8090-43b3-443b-bc26-b65e046c7825
-- title:
--   QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k =
      (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).effect a *
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ζ).effect b := by sorry
