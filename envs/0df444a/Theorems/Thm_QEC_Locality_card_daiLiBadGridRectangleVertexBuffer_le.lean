-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiBadGridRectangleVertexBuffer_le
-- name    : QEC.Locality.card_daiLiBadGridRectangleVertexBuffer_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:12:46.6261+00:00
-- url     : https://prove2.me/theorems/14d67686-99bd-43c7-937c-ff79a2491bb7
-- title:
--   Locality: card dai Li Bad Grid Rectangle Vertex Buffer le
-- statement:
--   The explicit finite bad-rectangle vertex buffer obeys the exact
--   `384 * ell^2 * M` packing charge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1187-L1229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1187-L1229

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

theorem QEC.Locality.card_daiLiBadGridRectangleVertexBuffer_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 1 ≤ ell)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) ≤
      384 * ell ^ 2 *
        ((∑ cell ∈ cells, (rectangles cell).length : Nat) : ℝ) := by sorry
