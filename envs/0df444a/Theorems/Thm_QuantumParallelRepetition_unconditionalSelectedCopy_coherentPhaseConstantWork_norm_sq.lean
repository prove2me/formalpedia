-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
-- name    : QuantumParallelRepetition.unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/f7bac965-e682-49e8-9ec2-aa44fff6c1bb
-- title:
--   QuantumParallelRepetition.unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
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

theorem QuantumParallelRepetition.unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ _ _ => work)‖ ^ 2 =
      ‖history‖ ^ 2 * ‖work‖ ^ 2 := by sorry
