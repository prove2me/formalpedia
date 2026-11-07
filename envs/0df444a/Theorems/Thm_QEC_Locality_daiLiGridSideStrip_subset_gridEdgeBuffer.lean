-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGridSideStrip_subset_gridEdgeBuffer
-- name    : QEC.Locality.daiLiGridSideStrip_subset_gridEdgeBuffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:53.147197+00:00
-- url     : https://prove2.me/theorems/15130926-59ff-44cb-9433-fb54622b60cc
-- title:
--   Locality: dai Li Grid Side Strip subset grid Edge Buffer
-- statement:
--   Every actual finite side strip lies in the corresponding periodic edge
--   event for the same translation.  Only this inclusion, not an identification
--   of a quotient cell with a physical region, is used for the #385 count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1539-L1594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1539-L1594

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

theorem QEC.Locality.daiLiGridSideStrip_subset_gridEdgeBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) (side : DaiLiGridSideIndex) :
    daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side ⊆
      Finset.univ.filter fun q => edgeBad w edgeRadius t (embedding.point q) := by sorry
