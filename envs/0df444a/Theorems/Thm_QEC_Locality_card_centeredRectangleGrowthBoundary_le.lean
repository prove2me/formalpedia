-- Prove2me | Theorems.Thm_QEC_Locality_card_centeredRectangleGrowthBoundary_le
-- name    : QEC.Locality.card_centeredRectangleGrowthBoundary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:48.021288+00:00
-- url     : https://prove2.me/theorems/a9863591-2fe7-4d64-92e6-71aadc924705
-- title:
--   Locality: card centered Rectangle Growth Boundary le
-- statement:
--   The actual rectangle-growth boundary is controlled by the four-strip
--   packing estimate and the true long-incidence counter of the inner rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L968-L999
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L968-L999

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.card_centeredRectangleGrowthBoundary_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
      outerVerticalRadius threshold).selected.card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by sorry
