-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCachedLedgerStoppingTransfer
-- name    : QuantumParallelRepetition.unconditionalActualFairCachedLedgerStoppingTransfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/466accb4-4a0d-46ff-a91d-4d0b714d8174
-- title:
--   QuantumParallelRepetition.unconditionalActualFairCachedLedgerStoppingTransfer
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
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairCachedLedgerStoppingTransfer
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (rational_normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (support_preserving : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {L : ℕ} {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (PA : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : ExactSourceSharedFlag X Y A B D denominator →
      X → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (V : ExactSourceSharedFlag X Y A B D denominator →
      Y → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (z : ExactSourceSharedFlag X Y A B D denominator →
      EuclideanSpace ℂ
        ((Σ r : Fin (L + 1), ι r) ×
          (Σ r : Fin (L + 1), ι r)))
    (z_normalized : ∀ flag, ‖z flag‖ = 1)
    (matched :
      ExactSourceSharedFlag X Y A B D denominator ×
        (X × Y) → Bool)
    {K : Type} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (actual canonical source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p)
    (epsilon lam deviation clipping bad : ℝ)
    (analytic :
      UnconditionalActualFairCachedStoppedAnalyticLedger
        (exactLocallySampleableLaw G n S D)
        actual canonical source deviation clipping bad)
    (verifier :
      UnconditionalActualFairCachedSourceVerifierLedger
        G n S D effect actual source)
    (source_failure :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < epsilon / 2)
    (total_variation :
      QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤ lam)
    (mismatch :
      (∑ outcome :
        ExactSourceSharedFlag X Y A B D denominator × (X × Y),
        flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
          if matched outcome then 0 else 1) ≤ 4 * lam)
    (matched_physical_branch :
      ∀ (flag : ExactSourceSharedFlag X Y A B D denominator)
        (x : X) (y : Y),
        matched (flag, (x, y)) = true →
          (∑ k : K,
            quadraticExpectation
              (effect
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))
              (actual
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))) ≤
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) :
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G
        (exactSourceSharedFlagWeight D denominator)
        (exactSourceSharedFlagWeight_nonneg D denominator)
        (exactSourceSharedFlagWeight_sum D remaining denominator)
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability := by sorry
