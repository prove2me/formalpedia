-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDInternalSideRawBounds
-- name    : QEC.Locality.mem_daiLiKGeDInternalSideRawBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:50.811896+00:00
-- url     : https://prove2.me/theorems/9fa3e3d5-2c48-4155-bb13-94938ca0ba64
-- title:
--   Locality: mem dai Li KGe DInternal Side Raw Bounds
-- statement:
--   Exact coordinate bounds for the raw upper-side strip of one canonical
--   internal cut.  The later pairwise proof uses these bounds before subtracting
--   the separator, so no geometric gap is hidden in a set-level wrapper.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3123-L3141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3123-L3141

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

theorem QEC.Locality.mem_daiLiKGeDInternalSideRawBounds
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).1
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2 3) :
    (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).1.1 + 2 * ell ≤
        (embedding.point q).1 ∧
      (embedding.point q).1 ≤
        (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.1 - 2 * ell ∧
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.2 - ell ≤
        (embedding.point q).2 ∧
      (embedding.point q).2 ≤
        (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.2 + ell := by sorry
