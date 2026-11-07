-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_leftCayleyGraph_symmetric
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.leftCayleyGraph_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:54:26.839532+00:00
-- url     : https://prove2.me/theorems/ae4a1768-a9c2-4fbc-ad5f-15d5d8e46968
-- title:
--   Left Right Cayley Square Complex: left Cayley Graph symmetric
-- statement:
--   The Left Right Cayley Square Complex construction uses the left Cayley Graph symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L118-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L118-L127

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.leftCayleyGraph_symmetric (X : LeftRightCayleySquareComplex G A B Square) :
    IsSymmetric X.leftCayleyGraph := by sorry
