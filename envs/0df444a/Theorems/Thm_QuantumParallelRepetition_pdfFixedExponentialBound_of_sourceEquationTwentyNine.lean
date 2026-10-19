-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfFixedExponentialBound_of_sourceEquationTwentyNine
-- name    : QuantumParallelRepetition.pdfFixedExponentialBound_of_sourceEquationTwentyNine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/e1f5a7da-643c-4367-93e0-402b04d0a710
-- title:
--   QuantumParallelRepetition.pdfFixedExponentialBound_of_sourceEquationTwentyNine
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.pdfFixedExponentialBound_of_sourceEquationTwentyNine
    (G : Game X Y A B) (n : ℕ) (d : ℝ)
    (construct :
      ∀ S : Strategy (G.repeat n),
        Real.exp (-d * (n : ℝ)) < S.winProbability →
          ∃ (rounded : Strategy G) (K₀ α η lam : ℝ),
            roundedWinningLowerBound (1 - entangledValue G)
                K₀ α η lam ≤ rounded.winProbability ∧
              totalSamplingLoss K₀ α η lam <
                (1 - entangledValue G) / 2) :
    repeatedEntangledValue G n ≤ Real.exp (-d * (n : ℝ)) := by sorry
