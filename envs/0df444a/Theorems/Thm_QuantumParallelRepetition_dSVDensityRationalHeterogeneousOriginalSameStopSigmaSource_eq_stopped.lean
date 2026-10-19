-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
-- name    : QuantumParallelRepetition.dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/dfb8cc91-ecd5-4c0e-9eb3-d758f216cc2a
-- title:
--   QuantumParallelRepetition.dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem QuantumParallelRepetition.dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ =
      dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ := by sorry
