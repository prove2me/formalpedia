-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_symmetric
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.unionCayleyGraph_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:31:38.370935+00:00
-- url     : https://prove2.me/theorems/c7be6e82-c7c4-44cf-a32d-6e2033a3a0a6
-- title:
--   Left Right Cayley Square Complex: union Cayley Graph symmetric
-- statement:
--   Inverse generator labels reverse the actual weighted edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L50-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L50-L68

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.unionCayleyGraph_symmetric
    (X : LeftRightCayleySquareComplex G A B Square) (g h : G) :
    X.unionCayleyGraph g h = X.unionCayleyGraph h g := by sorry
