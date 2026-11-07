-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_eventual_local_weight_reduction_of_mixing
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_eventual_local_weight_reduction_of_mixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:47.888224+00:00
-- url     : https://prove2.me/theorems/4ad21a2a-e91a-452c-9bf5-6196281c9a24
-- title:
--   Left Right Cayley Square Complex: exists eventual local weight reduction of mixing
-- statement:
--   For all sufficiently large fixed degrees, actual graph mixing and actual
--   puncture-resistant component codes construct a local reducing tensor check.
--   There is no reducing-check hypothesis in this theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L72-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L72-L168

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_eventual_local_weight_reduction_of_mixing
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square : Type v) [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square],
      ∀ (X : LeftRightCayleySquareComplex G A B Square), X.HasCayleyLinkIdentities →
      ∀ (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (dA dB : Nat),
      MinimumDistance CA dA → MinimumDistance CB dB →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust CA CB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance CA CB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
        (Nat.floor ((Delta : ℝ) ^ gamma)) →
      ∀ (side : Bool) (x : Word (ZMod 2) Square), x ≠ 0 →
      (∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier) →
      HasExpanderMixingBound (X.squareGraph side) (Delta * Delta) (4 * (Delta : ℝ)) →
      HasExpanderMixingBound X.unionCayleyGraph (Delta + Delta) (4 * Real.sqrt (Delta : ℝ)) →
      ((X.activeVerticesOnSide side x).card : ℝ) ≤
        Fintype.card G / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon)) →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
        HammingWeight (X.localRestriction (g, !side) x + c) <
          HammingWeight (X.localRestriction (g, !side) x) := by sorry
