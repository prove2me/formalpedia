-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_eventual_minimumDistance_ge_of_mixing
-- name    : QEC.Coding.QuantumTanner.Data.exists_eventual_minimumDistance_ge_of_mixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:57.0534+00:00
-- url     : https://prove2.me/theorems/4b4583bd-d0d6-44cb-86e4-54ee944c471d
-- title:
--   Data: exists eventual minimum Distance ge of mixing
-- statement:
--   The actual Quantum Tanner CSS minimum satisfies the source's global
--   distance bound when both local-code pairs have the source robustness and the
--   actual square and union graphs have the required mixing bounds. The primal
--   and dual sectors are proved separately; selected-family existence is not a
--   hypothesis disguised as a distance conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L187-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L187-L245

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

theorem QEC.Coding.QuantumTanner.Data.exists_eventual_minimumDistance_ge_of_mixing
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
      (∀ side, HasExpanderMixingBound (D.complex.squareGraph side) (Delta * Delta) (4 * (Delta : ℝ))) →
      HasExpanderMixingBound D.complex.unionCayleyGraph (Delta + Delta) (4 * Real.sqrt (Delta : ℝ)) →
      ∀ distance : Nat, AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode distance →
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤ (distance : ℝ) := by sorry
