-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfQuantitativeRoundingLoss
-- name    : QuantumParallelRepetition.pdfQuantitativeRoundingLoss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/2170febe-4e6e-4de2-911d-4dcfb7db3030
-- title:
--   QuantumParallelRepetition.pdfQuantitativeRoundingLoss
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

theorem QuantumParallelRepetition.pdfQuantitativeRoundingLoss
    {K alpha eta kappa gamma : ℝ}
    (constant : 0 ≤ K)
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K alpha eta (kappa + gamma) ≤
      2 * K * alpha ^ (1 / 12 : ℝ) +
        pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
        (5 + 2 * universalErrorCeiling K) * gamma := by sorry
