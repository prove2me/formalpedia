-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
-- name    : QEC.Coding.QuantumTanner.ArithmeticPSLFamily.positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:22:17.683381+00:00
-- url     : https://prove2.me/theorems/58f0d8fe-a6f6-415e-9e63-1d5457501e2c
-- title:
--   Arithmetic PSLFamily: positive Probability good arithmetic family of complex spectral bounds
-- statement:
--   The source's nonzero-probability formulation for one uniform matrix draw.
--   The degree is fixed before this draw and before the cofinal family grows.
--   The finite-uniform event equivalence is already proved in `Goodness`; it adds
--   no random-code, geometric, rate, distance, or spectral assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGoodness.lean#L136-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGoodness.lean#L136-L165

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion
variable (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
  (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)

theorem QEC.Coding.QuantumTanner.ArithmeticPSLFamily.positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2)
    (hRamanujan : ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → ∀ n : ℕ,
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) (N : ℕ) :
    ∃ (p : ℕ) (hPrime : p.Prime),
      letI : Fact p.Prime := ⟨hPrime⟩
      ∃ (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
        N ≤ p + 1 ∧ (∀ r : ZMod p, r ^ 2 ≠ epsilon) ∧
        HasPositiveUniformProbability
          (HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
            (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
            (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
            (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
            (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1)) := by sorry
