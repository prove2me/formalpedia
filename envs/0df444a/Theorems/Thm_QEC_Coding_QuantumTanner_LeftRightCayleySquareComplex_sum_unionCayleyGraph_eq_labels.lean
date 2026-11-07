-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_unionCayleyGraph_eq_labels
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_unionCayleyGraph_eq_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:30:47.213974+00:00
-- url     : https://prove2.me/theorems/3ed730c5-3cab-4f62-b103-cad598564642
-- title:
--   Left Right Cayley Square Complex: sum union Cayley Graph eq labels
-- statement:
--   Count generator labels entering a vertex set, without discarding multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L32-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L32-L40

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_unionCayleyGraph_eq_labels
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (T : Finset G) :
    (∑ h ∈ T, X.unionCayleyGraph g h) =
      (Finset.univ.filter fun a => X.leftGenerator a * g ∈ T).card +
      (Finset.univ.filter fun b => g * X.rightGenerator b ∈ T).card := by sorry
