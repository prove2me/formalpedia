-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_normal_cover_of_robust
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_normal_cover_of_robust
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:57:52.309206+00:00
-- url     : https://prove2.me/theorems/f08958e5-82a8-46a3-8c25-eff335de6005
-- title:
--   Left Right Cayley Square Complex: exists normal cover of robust
-- statement:
--   Robustness supplies the actual small covers at every nonexceptional
--   neighbor, including zero local views outside the active set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L123-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L123-L153

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_normal_cover_of_robust
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w normalCutoff : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hCutoff : 0 < normalCutoff)
    (hWeightBudget : normalCutoff - 1 ≤ w)
    (hRows : (normalCutoff - 1) / dB < dA)
    (hColumns : (normalCutoff - 1) / dA < dB)
    (side : Bool) (x : Word (ZMod 2) Square)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (g : G) (hg : g ∉ X.exceptionalVerticesOnSide side x normalCutoff) :
    ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      rows.card ≤ (normalCutoff - 1) / dB ∧
      columns.card ≤ (normalCutoff - 1) / dA := by sorry
