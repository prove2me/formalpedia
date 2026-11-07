-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_mem
-- name    : QEC.Locality.daiLiKGeDRegionRectangle_bad_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:20.859532+00:00
-- url     : https://prove2.me/theorems/ef207cb6-aa7e-4364-91f6-de60c9756d99
-- title:
--   Locality: dai Li KGe DRegion Rectangle bad mem
-- statement:
--   Every in-range bad-region index denotes an actual member of its cell's
--   #496 rectangle list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2337-L2344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2337-L2344

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

theorem QEC.Locality.daiLiKGeDRegionRectangle_bad_mem
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length) :
    daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr (cell, slot)) ∈
      rectangles cell := by sorry
