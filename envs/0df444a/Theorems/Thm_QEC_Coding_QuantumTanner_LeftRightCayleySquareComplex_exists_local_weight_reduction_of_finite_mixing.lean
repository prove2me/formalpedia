-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_local_weight_reduction_of_finite_mixing
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_weight_reduction_of_finite_mixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:12.483055+00:00
-- url     : https://prove2.me/theorems/76d2e92f-65d6-48f5-8d9b-0e80d7b2ce41
-- title:
--   Left Right Cayley Square Complex: exists local weight reduction of finite mixing
-- statement:
--   Actual finite mixing, local-code robustness and explicit scalar budgets
--   construct a local tensor check decreasing any given nonzero word whose local
--   views lie in the corresponding dual-tensor code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalDescent.lean#L39-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalDescent.lean#L39-L151

import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_weight_reduction_of_finite_mixing
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w p normalCutoff heavyCutoff : Nat)
    (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hCard : Fintype.card A = Fintype.card B)
    (hDegree : 0 < Fintype.card A + Fintype.card B)
    (hp : p ≤ Fintype.card A) (hpA : p < dA) (hpB : p < dB)
    (hRobust : IsRobust CA CB w)
    (hPunctures : IsRobustWithPunctureResistance CA CB w p)
    (hPunctureBudget : 2 * w ≤ (dA - p) * (dB - p))
    (hNormalCutoff : 0 < normalCutoff) (hWeightBudget : normalCutoff - 1 ≤ w)
    (hRows : (normalCutoff - 1) / dB < dA)
    (hColumns : (normalCutoff - 1) / dA < dB)
    (hHeavyRows : heavyCutoff + (normalCutoff - 1) / dA ≤ dB)
    (hHeavyColumns : heavyCutoff + (normalCutoff - 1) / dB ≤ dA)
    (hErrorBudget : Fintype.card B * ((normalCutoff - 1) / dB) +
      Fintype.card A * ((normalCutoff - 1) / dA) ≤ w)
    (side : Bool) (x : Word (ZMod 2) Square) (hx : x ≠ 0)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (squareSpectral unionSpectral normalThreshold gap fraction ratio uniformBudget threshold : ℝ)
    (hSquareSpectral : 0 ≤ squareSpectral) (hUnionSpectral : 0 ≤ unionSpectral)
    (hNormalThreshold : 0 < normalThreshold) (hNormalRound : normalThreshold ≤ normalCutoff)
    (hGap : 0 < gap) (hFraction : 0 ≤ fraction) (hFractionHalf : fraction ≤ 1 / 2)
    (hThreshold : 0 < threshold)
    (hSquareMixing : HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) squareSpectral)
    (hUnionMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) unionSpectral)
    (hSquareSmall : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤ normalThreshold * Fintype.card G)
    (hFractionBudget : 4 * squareSpectral ^ 2 ≤ fraction * normalThreshold ^ 2)
    (hUnionDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card + gap * Fintype.card G ≤
      (heavyCutoff : ℝ) * Fintype.card G)
    (hRatioBudget : unionSpectral ^ 2 ≤ ratio * gap ^ 2)
    (hAverageBudget : 2 * threshold * ratio ≤ 1 - fraction)
    (hMeanBudget : (Fintype.card A + Fintype.card B : Nat) *
      (fraction * (X.activeVerticesOnSide side x).card) ≤ uniformBudget * Fintype.card G)
    (hSelectionBudget : (uniformBudget + unionSpectral * Real.sqrt
      (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) *
      (Fintype.card A + Fintype.card B : Nat) ≤ (p : ℝ) * threshold)
    (hMargin : (3 * (Fintype.card B * ((normalCutoff - 1) / dB) +
      Fintype.card A * ((normalCutoff - 1) / dA)) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
      (heavyCutoff : ℝ) * threshold) :
    ∃ g : G, ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, !side) x + c) <
        HammingWeight (X.localRestriction (g, !side) x) := by sorry
