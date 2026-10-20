-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
-- name    : QuantumParallelRepetition.dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/b30bc331-361f-4141-a425-abaa8c8f9a3a
-- title:
--   QuantumParallelRepetition.dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
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

theorem QuantumParallelRepetition.dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (q : Fin j.val →
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d)) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
        width schedule ξ ζ j q =
      ∏ i : Fin j.val,
        dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          ⟨i.val, by omega⟩ (q i) := by sorry
