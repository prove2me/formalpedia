-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
-- name    : QuantumParallelRepetition.unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/4c5ad841-b509-4d05-9bc1-fa908a1ffb8a
-- title:
--   QuantumParallelRepetition.unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
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
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (u : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D u ≠ 0) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ u.2.1 u.2.2.1))
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D u.2.2.2
            u.2.1 u.2.2.1))) =
    exactSourceConditionalWinningProbability G n S D u := by sorry
