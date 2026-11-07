-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiKGeDSeparator_le
-- name    : QEC.Locality.card_daiLiKGeDSeparator_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:13:35.594064+00:00
-- url     : https://prove2.me/theorems/5d596ad9-820c-4783-ba03-b3ec13a93e1f
-- title:
--   Locality: card dai Li KGe DSeparator le
-- statement:
--   The `k >= d` separator has a concrete componentwise cardinality estimate.
--   The first term is exactly the selected grid-vertex count, the second is the
--   actual global long-endpoint count, and the third is the constructed rectangle
--   vertex charge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1247-L1297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1247-L1297

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

theorem QEC.Locality.card_daiLiKGeDSeparator_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by sorry
