-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalStoppedPhaseHarmonic_distance_sq
-- name    : QuantumParallelRepetition.unconditionalStoppedPhaseHarmonic_distance_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/8c013c6c-d12a-48d0-be0e-46e6d587ebd8
-- title:
--   QuantumParallelRepetition.unconditionalStoppedPhaseHarmonic_distance_sq
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

theorem QuantumParallelRepetition.unconditionalStoppedPhaseHarmonic_distance_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : EuclideanSpace ℂ (H × H)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => embezzlementState m) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => embezzlementState m)‖ ^ 2 =
      ‖x - y‖ ^ 2 := by sorry
