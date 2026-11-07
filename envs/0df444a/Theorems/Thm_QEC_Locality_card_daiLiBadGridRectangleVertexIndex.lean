-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiBadGridRectangleVertexIndex
-- name    : QEC.Locality.card_daiLiBadGridRectangleVertexIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:12:44.615203+00:00
-- url     : https://prove2.me/theorems/a185bcdb-3f59-4696-b371-c765f200de59
-- title:
--   Locality: card dai Li Bad Grid Rectangle Vertex Index
-- statement:
--   The Locality construction uses the card dai Li Bad Grid Rectangle Vertex Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1153-L1167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1153-L1167

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.card_daiLiBadGridRectangleVertexIndex
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Fintype.card (DaiLiBadGridRectangleVertexIndex cells rectangles) =
      4 * ∑ cell ∈ cells, (rectangles cell).length := by sorry
