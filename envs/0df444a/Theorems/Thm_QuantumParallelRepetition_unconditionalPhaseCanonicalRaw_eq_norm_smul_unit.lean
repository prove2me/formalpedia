-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
-- name    : QuantumParallelRepetition.unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/656a188a-e06f-43ed-b8fb-75bad15f249a
-- title:
--   QuantumParallelRepetition.unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
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

theorem QuantumParallelRepetition.unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B
        (unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedTarget
            w N gamma))
        (fun _ _ _ => embezzlementState m) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m) := by sorry
