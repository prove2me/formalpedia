-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_totalSamplingLoss_mono
-- name    : QuantumParallelRepetition.exact_totalSamplingLoss_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/bcafe0ab-2eea-4587-b6dc-3cc78f5f79c4
-- title:
--   QuantumParallelRepetition.exact_totalSamplingLoss_mono
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
open Filter
open scoped Topology
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exact_totalSamplingLoss_mono
    {K₀ α₁ α₂ η₁ η₂ lam₁ lam₂ : ℝ}
    (constant_nonnegative : 0 ≤ K₀)
    (alpha_nonnegative : 0 ≤ α₁)
    (alpha_le : α₁ ≤ α₂)
    (eta_nonnegative : 0 ≤ η₁)
    (eta_le : η₁ ≤ η₂)
    (lam_le : lam₁ ≤ lam₂) :
    totalSamplingLoss K₀ α₁ η₁ lam₁ ≤
      totalSamplingLoss K₀ α₂ η₂ lam₂ := by sorry
