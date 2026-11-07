-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptional_crossCount_le_of_heavy_coverage
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_crossCount_le_of_heavy_coverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:57:53.559293+00:00
-- url     : https://prove2.me/theorems/67d5f583-744d-42d9-ad59-8b183d9f3f8c
-- title:
--   Left Right Cayley Square Complex: exceptional cross Count le of heavy coverage
-- statement:
--   Derive the bad-incidence budget from actual mixing, exceptional-set size,
--   and heavy coverage, instead of postulating the bad-incidence sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean#L121-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean#L121-L147

import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_crossCount_le_of_heavy_coverage
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (S exceptional : Finset G) (spectral fraction uniformBudget : ℝ)
    (hSpectral : 0 ≤ spectral) (hFraction : 0 ≤ fraction)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) spectral)
    (hExceptional : 2 * (S ∩ exceptional).card ≤ S.card)
    (hFractionBound : (exceptional.card : ℝ) ≤ fraction * S.card)
    (hMean : (Fintype.card A + Fintype.card B : Nat) * (exceptional.card : ℝ) ≤
      uniformBudget * Fintype.card G)
    (hCoverage : (S \ exceptional).card ≤
      crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional))) :
    (crossCount X.unionCayleyGraph exceptional
      (X.oppositeHeavySet side x cutoff (S \ exceptional)) : ℝ) ≤
      (uniformBudget + spectral * Real.sqrt
        (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) *
      (X.oppositeHeavySet side x cutoff (S \ exceptional)).card := by sorry
