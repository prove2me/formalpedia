-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSmallSourcePhysicalRoundedLower
-- name    : QuantumParallelRepetition.unconditionalSmallSourcePhysicalRoundedLower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/0cc226a2-83b8-4ed0-a733-9ebd33d2195a
-- title:
--   QuantumParallelRepetition.unconditionalSmallSourcePhysicalRoundedLower
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

theorem QuantumParallelRepetition.unconditionalSmallSourcePhysicalRoundedLower
    (K eta alpha deviation clipping epsilon lam actual : ℝ)
    (constant :
      1024 + 8 *
          (4 * Real.sqrt
            (34 + unconditionalPrefactorBucketCoefficient) + 2) ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small :
      64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2))
    (lam_nonnegative : 0 ≤ lam)
    (actual_original_verifier :
      1 - epsilon / 2 - 5 * lam -
        ((64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt deviation + 4 * Real.sqrt clipping +
          2 * Real.sqrt (8 * eta)) ≤ actual) :
    roundedWinningLowerBound epsilon K alpha eta lam ≤ actual := by sorry
