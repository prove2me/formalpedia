-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_eventual_minimumDistance_ge_of_cayley_spectral
-- name    : QEC.Coding.QuantumTanner.Data.exists_eventual_minimumDistance_ge_of_cayley_spectral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:30.790178+00:00
-- url     : https://prove2.me/theorems/85229e2f-eb67-4971-a793-725f67a59208
-- title:
--   Data: exists eventual minimum Distance ge of cayley spectral
-- statement:
--   The same global distance theorem with only the actual left/right Cayley
--   spectral estimates as graph inputs. The square and union mixing hypotheses
--   are now derived, rather than separately supplied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L250-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L250-L293

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.Data
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.exists_eventual_minimumDistance_ge_of_cayley_spectral
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis), D.complex.HasCayleyLinkIdentities →
      ∀ (dA dB dADual dBDual : Nat),
      MinimumDistance D.codeA dA → MinimumDistance D.codeB dB →
      MinimumDistance D.codeA.dual dADual → MinimumDistance D.codeB.dual dBDual →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      delta * Delta ≤ (dADual : ℝ) → delta * Delta ≤ (dBDual : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust D.codeA D.codeB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobust D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance D.codeA D.codeB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      IsRobustWithPunctureResistance D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      HasMeanZeroBilinearBound D.complex.leftCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      HasMeanZeroBilinearBound D.complex.rightCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      ∀ distance : Nat, AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode distance →
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤ (distance : ℝ) := by sorry
