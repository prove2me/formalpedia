-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
-- name    : QuantumParallelRepetition.dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/8ccfaca9-5c86-47b3-b968-aac27e7bdfdb
-- title:
--   QuantumParallelRepetition.dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
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
open scoped BigOperators ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine ξ).val‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by sorry
