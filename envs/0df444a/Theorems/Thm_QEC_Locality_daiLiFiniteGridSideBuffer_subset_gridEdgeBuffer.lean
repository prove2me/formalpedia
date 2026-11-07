-- Prove2me | Theorems.Thm_QEC_Locality_daiLiFiniteGridSideBuffer_subset_gridEdgeBuffer
-- name    : QEC.Locality.daiLiFiniteGridSideBuffer_subset_gridEdgeBuffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:17:28.346198+00:00
-- url     : https://prove2.me/theorems/dfc46e79-7c92-4831-9755-421e244154b8
-- title:
--   Locality: dai Li Finite Grid Side Buffer subset grid Edge Buffer
-- statement:
--   The entire finite physical side buffer is counted by the matching periodic
--   edge event selected by the averaging theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1598-L1607
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1598-L1607

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

theorem QEC.Locality.daiLiFiniteGridSideBuffer_subset_gridEdgeBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) :
    daiLiFiniteGridSideBuffer embedding w edgeRadius vertexRadius origin ⊆
      Finset.univ.filter fun q => edgeBad w edgeRadius t (embedding.point q) := by sorry
