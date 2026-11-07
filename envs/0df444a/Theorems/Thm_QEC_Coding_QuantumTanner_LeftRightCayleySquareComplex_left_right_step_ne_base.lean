-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_left_right_step_ne_base
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.left_right_step_ne_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:36:53.610379+00:00
-- url     : https://prove2.me/theorems/15a1ec4c-a51b-4cac-9c9d-4e96fafc453c
-- title:
--   Left Right Cayley Square Complex: left right step ne base
-- statement:
--   TNC excludes a same-side loop for every pair of actual generator labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L36-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L36-L42

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.left_right_step_ne_base
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (a : A) (b : B) :
    X.leftGenerator a * g * X.rightGenerator b ≠ g := by sorry
