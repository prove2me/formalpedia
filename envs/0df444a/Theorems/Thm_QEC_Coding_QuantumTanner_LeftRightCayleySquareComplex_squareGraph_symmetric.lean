-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_symmetric
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:37:33.47744+00:00
-- url     : https://prove2.me/theorems/29cd58cc-e2e1-4d02-ba33-cd870d65b3dd
-- title:
--   Left Right Cayley Square Complex: square Graph symmetric
-- statement:
--   The Left Right Cayley Square Complex construction uses the square Graph symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L35-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L35-L41

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_symmetric (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) : IsSymmetric (X.squareGraph side) := by sorry
