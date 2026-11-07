-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_left_neighbor_mem_active_of_entry_ne_zero
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.left_neighbor_mem_active_of_entry_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:51:26.773046+00:00
-- url     : https://prove2.me/theorems/659572cb-cc19-40b3-85c9-7e362ffe8749
-- title:
--   Left Right Cayley Square Complex: left neighbor mem active of entry ne zero
-- statement:
--   Each nonzero link entry has an actually active left neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L116-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L116-L127

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.left_neighbor_mem_active_of_entry_ne_zero
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) (b : B)
    (hEntry : X.localRestriction (g, side) x (a, b) ≠ 0) :
    X.leftGenerator a * g ∈ X.activeVerticesOnSide (!side) x := by sorry
