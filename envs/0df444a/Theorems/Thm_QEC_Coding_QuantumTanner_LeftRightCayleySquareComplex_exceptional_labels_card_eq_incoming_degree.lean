-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptional_labels_card_eq_incoming_degree
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_labels_card_eq_incoming_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:08.710193+00:00
-- url     : https://prove2.me/theorems/daf63b9d-0f53-4cda-80dc-c85fb3455769
-- title:
--   Left Right Cayley Square Complex: exceptional labels card eq incoming degree
-- statement:
--   The selected vertex's bad incoming degree counts both kinds of bad labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L156-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L156-L165

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_labels_card_eq_incoming_degree
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (exceptional : Finset G) :
    (X.exceptionalLeftLabels g exceptional).card +
      (X.exceptionalRightLabels g exceptional).card =
      ∑ h ∈ exceptional, X.unionCayleyGraph h g := by sorry
