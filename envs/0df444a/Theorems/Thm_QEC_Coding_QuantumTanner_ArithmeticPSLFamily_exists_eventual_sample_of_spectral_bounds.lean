-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_exists_eventual_sample_of_spectral_bounds
-- name    : QEC.Coding.QuantumTanner.ArithmeticPSLFamily.exists_eventual_sample_of_spectral_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:04:49.633448+00:00
-- url     : https://prove2.me/theorems/02398144-1639-4663-8cc1-11f503f7ff92
-- title:
--   Arithmetic PSLFamily: exists eventual sample of spectral bounds
-- statement:
--   At a sufficiently large fixed prime degree, only the two concrete spectral
--   estimates are still inputs to the full same-sample global parameter theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGoodness.lean#L40-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGoodness.lean#L40-L79

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

theorem QEC.Coding.QuantumTanner.ArithmeticPSLFamily.exists_eventual_sample_of_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : ℕ, ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → t ≤ p + 1 →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho (p + 1))
        (TorusIndex epsilon) (TorusIndex epsilon),
      (∀ n, HasMeanZeroBilinearBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      (∀ n, HasMeanZeroBilinearBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
        (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
        (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
        (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
        (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1) sample := by sorry
