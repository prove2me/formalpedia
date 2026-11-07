-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_link_rebase_both
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.link_rebase_both
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:55:34.610328+00:00
-- url     : https://prove2.me/theorems/65918427-5b6b-43c8-b39a-a6e407a2a291
-- title:
--   Left Right Cayley Square Complex: link rebase both
-- statement:
--   Rebase a square at its other vertex on the same side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L26-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L26-L33

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.link_rebase_both
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (g : G) (side : Bool) (a : A) (b : B) :
    X.link (g, side) (a, b) =
      X.link (X.leftGenerator a * g * X.rightGenerator b, side)
        (X.leftInverse a, X.rightInverse b) := by sorry
