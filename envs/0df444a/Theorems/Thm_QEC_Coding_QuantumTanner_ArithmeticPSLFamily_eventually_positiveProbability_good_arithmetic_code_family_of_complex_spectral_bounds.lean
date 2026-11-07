-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_eventually_positiveProbability_good_arithmetic_code_family_of_complex_spectral_bounds
-- name    : QEC.Coding.QuantumTanner.ArithmeticPSLFamily.eventually_positiveProbability_good_arithmetic_code_family_of_complex_spectral_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:44:06.060977+00:00
-- url     : https://prove2.me/theorems/7285c8df-6e49-4576-bff7-1daef07815ab
-- title:
--   Arithmetic PSLFamily: eventually positive Probability good arithmetic code family of complex spectral bounds
-- statement:
--   Public semantic form of the conditional fixed-degree theorem. The family
--   in the conclusion is the canonical code family built from the same uniform
--   local-matrix draw, not an unrelated witness or an assumed goodness field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/ConditionalQuantumTannerFamily.lean#L41-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/ConditionalQuantumTannerFamily.lean#L41-L81

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
import Definitions.Def_QEC_Results_QLDPC_ConditionalQuantumTannerFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion
attribute [local irreducible] fintypeTorusIndex cayleySquareFintype Family.ofData

theorem QEC.Coding.QuantumTanner.ArithmeticPSLFamily.eventually_positiveProbability_good_arithmetic_code_family_of_complex_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : ℕ, ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → t ≤ p + 1 →
      (∀ n : ℕ,
        HasMeanZeroComplexOperatorBound
          (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
          (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
        HasMeanZeroComplexOperatorBound
          (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
          (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      HasPositiveUniformProbability (fun sample =>
        HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
          (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
          (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
          (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
          (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1) sample ∧
        letI : ∀ n, DecidableEq (CayleySquare
            (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)) :=
          fun _ => Subtype.instDecidableEq
        let family := sampleFamily p hOdd epsilon hEpsilon rho sample
        ∃ hCofinal : ∀ N : ℕ, ∃ n, N ≤ (family n).blockLength,
          _root_.QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
            (Family.ofData family hCofinal)) := by sorry
