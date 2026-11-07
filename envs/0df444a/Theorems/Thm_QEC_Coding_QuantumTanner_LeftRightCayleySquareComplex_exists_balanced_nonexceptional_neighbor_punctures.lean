-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_balanced_nonexceptional_neighbor_punctures
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_balanced_nonexceptional_neighbor_punctures
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:01.940759+00:00
-- url     : https://prove2.me/theorems/8e9a0de3-0cd2-4f1e-9704-6fa798817935
-- title:
--   Left Right Cayley Square Complex: exists balanced nonexceptional neighbor punctures
-- statement:
--   Absorb all actual exceptional labels into matching punctures. Every
--   retained row and column then has a nonexceptional neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L169-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L169-L187

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_balanced_nonexceptional_neighbor_punctures
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (exceptional : Finset G)
    (p : Nat) (hCard : Fintype.card A = Fintype.card B) (hp : p ≤ Fintype.card A)
    (hBad : (∑ h ∈ exceptional, X.unionCayleyGraph h g) ≤ p) :
    ∃ removedA : Finset A, ∃ removedB : Finset B,
      removedA.card = removedB.card ∧ removedA.card ≤ p ∧
      (∀ a : KeptCoordinate removedA, X.leftGenerator a.1 * g ∉ exceptional) ∧
      (∀ b : KeptCoordinate removedB, g * X.rightGenerator b.1 ∉ exceptional) := by sorry
