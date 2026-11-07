-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_heavyUnionGraph_eq_labels
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_heavyUnionGraph_eq_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:53:10.258699+00:00
-- url     : https://prove2.me/theorems/ed811e82-9c98-4b69-ac7b-64ac11e71285
-- title:
--   Left Right Cayley Square Complex: sum heavy Union Graph eq labels
-- statement:
--   The total heavy degree counts precisely the heavy row and column labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L239-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L239-L270

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_heavyUnionGraph_eq_labels
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (g : G) :
    (∑ h : G, X.heavyUnionGraph side x cutoff g h) =
      (Finset.univ.filter fun a => cutoff ≤
        HammingWeight (rowRestriction a (X.localRestriction (g, side) x))).card +
      (Finset.univ.filter fun b => cutoff ≤
        HammingWeight (columnRestriction b (X.localRestriction (g, side) x))).card := by sorry
