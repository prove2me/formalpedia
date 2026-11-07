-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_local_reduction_of_punctured_line_approximations
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_reduction_of_punctured_line_approximations
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:12:51.332376+00:00
-- url     : https://prove2.me/theorems/b5625930-678b-4dc8-a1d1-29e20ee1909d
-- title:
--   Left Right Cayley Square Complex: exists local reduction of punctured line approximations
-- statement:
--   A selected normal neighborhood satisfying the numerical error margin
--   has an attained local tensor check that strictly reduces its weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L79-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L79-L109

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_reduction_of_punctured_line_approximations
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool)
    (removedA : Finset A) (removedB : Finset B)
    (dA dB w rowError columnError : Nat)
    (hA : MinimumDistance (puncturedCode CA removedA) dA)
    (hB : MinimumDistance (puncturedCode CB removedB) dB)
    (hRobust : IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w)
    (hBudget : 2 * w ≤ dA * dB)
    (hRows : ∀ a : KeptCoordinate removedA, ∃ r : Word (ZMod 2) B,
      r ∈ CB.carrier ∧
      HammingWeight (rowRestriction a.1 (X.localRestriction (g, side) x) + r) ≤ rowError)
    (hColumns : ∀ b : KeptCoordinate removedB, ∃ c : Word (ZMod 2) A,
      c ∈ CA.carrier ∧
      HammingWeight (columnRestriction b.1 (X.localRestriction (g, side) x) + c) ≤ columnError)
    (hErrors : Fintype.card B * columnError + Fintype.card A * rowError ≤ w)
    (hMargin : 3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (removedA.card * Fintype.card B + Fintype.card A * removedB.card) <
      2 * HammingWeight (X.localRestriction (g, side) x)) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, side) x + c) <
        HammingWeight (X.localRestriction (g, side) x) := by sorry
