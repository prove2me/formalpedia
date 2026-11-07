-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_high_heavy_low_exceptional_vertex
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_high_heavy_low_exceptional_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:56:37.835188+00:00
-- url     : https://prove2.me/theorems/2a9704fe-147e-407b-a750-2a3a49e67a16
-- title:
--   Left Right Cayley Square Complex: exists high heavy low exceptional vertex
-- statement:
--   Select an actual opposite vertex using a heavy-coverage lower bound and
--   an actual exceptional-incidence upper bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean#L26-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean#L26-L92

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_high_heavy_low_exceptional_vertex
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (normal exceptional : Finset G) (hNormal : normal.Nonempty)
    (hDegreePositive : 0 < Fintype.card A + Fintype.card B)
    (threshold badAverage badCutoff : ℝ)
    (hThreshold : 0 < threshold) (hCutoff : 0 ≤ badCutoff)
    (hHeavyCoverage : normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal))
    (hUsefulAverage : 2 * threshold * (X.oppositeHeavySet side x cutoff normal).card ≤
      (normal.card : ℝ))
    (hBadAverage : (crossCount X.unionCayleyGraph exceptional
      (X.oppositeHeavySet side x cutoff normal) : ℝ) ≤
      badAverage * (X.oppositeHeavySet side x cutoff normal).card)
    (hBudgets : badAverage * (Fintype.card A + Fintype.card B : Nat) ≤
      badCutoff * threshold) :
    ∃ h ∈ X.oppositeHeavySet side x cutoff normal,
      threshold ≤ (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h : Nat) ∧
      (∑ g ∈ exceptional, X.unionCayleyGraph g h : Nat) ≤ badCutoff := by sorry
