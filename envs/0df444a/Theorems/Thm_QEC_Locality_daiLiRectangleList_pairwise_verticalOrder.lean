-- Prove2me | Theorems.Thm_QEC_Locality_daiLiRectangleList_pairwise_verticalOrder
-- name    : QEC.Locality.daiLiRectangleList_pairwise_verticalOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:47.785116+00:00
-- url     : https://prove2.me/theorems/d61e4e50-201f-4f2e-9e2b-ab226b6755ea
-- title:
--   Locality: dai Li Rectangle List pairwise vertical Order
-- statement:
--   An ordered vertical rectangle chain becomes pairwise ordered once every
--   member has nonnegative height.  This is the list-level geometry behind the
--   strict `ell` cores of a bad-cell subdivision.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L553-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L553-L582

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

theorem QEC.Locality.daiLiRectangleList_pairwise_verticalOrder
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hChain : rectangles.IsChain (fun first second => first.2.2 = second.1.2))
    (hNonnegative : ∀ rectangle ∈ rectangles,
      0 ≤ rectangle.2.2 - rectangle.1.2) :
    rectangles.Pairwise (fun first second => first.2.2 ≤ second.1.2) := by sorry
