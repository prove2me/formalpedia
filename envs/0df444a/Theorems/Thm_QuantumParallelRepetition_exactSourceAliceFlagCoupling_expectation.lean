-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceAliceFlagCoupling_expectation
-- name    : QuantumParallelRepetition.exactSourceAliceFlagCoupling_expectation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/506a6f23-7bb7-47c6-b393-a8a79d5f1333
-- title:
--   QuantumParallelRepetition.exactSourceAliceFlagCoupling_expectation
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]

theorem QuantumParallelRepetition.exactSourceAliceFlagCoupling_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome *
        value (exactSourceAliceSampleTuple
          D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D history *
          value history := by sorry
