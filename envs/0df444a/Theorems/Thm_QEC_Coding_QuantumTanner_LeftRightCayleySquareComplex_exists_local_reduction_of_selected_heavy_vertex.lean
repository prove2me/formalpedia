-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_local_reduction_of_selected_heavy_vertex
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_reduction_of_selected_heavy_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:57:52.36709+00:00
-- url     : https://prove2.me/theorems/8af17e92-d4ac-402b-9743-236fb27b5686
-- title:
--   Left Right Cayley Square Complex: exists local reduction of selected heavy vertex
-- statement:
--   A genuinely selected heavy vertex produces a reducing tensor check.
--   Matching punctures, punctured minimum distances, attained approximations and
--   the check itself are all constructed from the actual codes and incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L192-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L192-L263

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_reduction_of_selected_heavy_vertex
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w p : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hCard : Fintype.card A = Fintype.card B) (hp : p ≤ Fintype.card A)
    (hpA : p < dA) (hpB : p < dB)
    (hRobust : IsRobustWithPunctureResistance CA CB w p)
    (hBudget : 2 * w ≤ (dA - p) * (dB - p))
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (normal exceptional : Finset G) (g : G) (threshold : ℝ)
    (hHeavy : threshold ≤ (∑ h ∈ normal, X.heavyUnionGraph side x cutoff h g : Nat))
    (hBad : (∑ h ∈ exceptional, X.unionCayleyGraph h g) ≤ p)
    (rowError columnError : Nat)
    (hCovers : ∀ h ∉ exceptional, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (h, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (h, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      rows.card ≤ columnError ∧ columns.card ≤ rowError)
    (hErrors : Fintype.card B * columnError + Fintype.card A * rowError ≤ w)
    (hMargin : (3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
      (cutoff : ℝ) * threshold) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, !side) x + c) <
        HammingWeight (X.localRestriction (g, !side) x) := by sorry
