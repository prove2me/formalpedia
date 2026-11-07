-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_right_neighbor_mem_active_of_entry_ne_zero
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.right_neighbor_mem_active_of_entry_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:51:50.051682+00:00
-- url     : https://prove2.me/theorems/b4a6abc8-81d7-4555-9d41-43318169e412
-- title:
--   Left Right Cayley Square Complex: right neighbor mem active of entry ne zero
-- statement:
--   Each nonzero link entry has an actually active right neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L130-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L130-L141

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.right_neighbor_mem_active_of_entry_ne_zero
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) (b : B)
    (hEntry : X.localRestriction (g, side) x (a, b) ≠ 0) :
    g * X.rightGenerator b ∈ X.activeVerticesOnSide (!side) x := by sorry
