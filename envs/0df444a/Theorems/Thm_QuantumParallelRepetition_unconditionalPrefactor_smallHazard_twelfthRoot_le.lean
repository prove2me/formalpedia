-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_smallHazard_twelfthRoot_le
-- name    : QuantumParallelRepetition.unconditionalPrefactor_smallHazard_twelfthRoot_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/ec7da1eb-c76d-403b-b8b8-21a7d77b0a88
-- title:
--   QuantumParallelRepetition.unconditionalPrefactor_smallHazard_twelfthRoot_le
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

theorem QuantumParallelRepetition.unconditionalPrefactor_smallHazard_twelfthRoot_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Real.sqrt
      ((34 / Real.sqrt
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
        unconditionalPrefactorBucketCoefficient *
          Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by sorry
