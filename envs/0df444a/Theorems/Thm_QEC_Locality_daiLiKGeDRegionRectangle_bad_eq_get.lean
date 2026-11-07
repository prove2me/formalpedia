-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_eq_get
-- name    : QEC.Locality.daiLiKGeDRegionRectangle_bad_eq_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:06.6113+00:00
-- url     : https://prove2.me/theorems/6cb6fb71-fdaf-42bf-96fb-ce2094a68835
-- title:
--   Locality: dai Li KGe DRegion Rectangle bad eq get
-- statement:
--   On an in-range bad index, the total lookup used by the region definition
--   reduces to the corresponding concrete list entry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2326-L2333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2326-L2333

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

theorem QEC.Locality.daiLiKGeDRegionRectangle_bad_eq_get
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length) :
    daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr (cell, slot)) =
      (rectangles cell).get ⟨slot, hSlot⟩ := by sorry
