-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
-- name    : QuantumParallelRepetition.unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/e0d6fb0a-00e6-4a08-bd9f-f0e7932bcbe5
-- title:
--   QuantumParallelRepetition.unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
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
open scoped BigOperators
open QuantumParallelRepetition.ClassicalSampling

theorem QuantumParallelRepetition.unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) :
    exactGlobalHistoryFinGamma G n S D
        (exactSourceAlicePermutationHistory
          D denominator numerator nonempty flag x) x =
      exactGlobalHistoryFinGamma G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 x := by sorry
