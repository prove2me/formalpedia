-- Prove2me | Theorems.Thm_QEC_Locality_card_centeredRectangleGeneralGrowthBoundary_le
-- name    : QEC.Locality.card_centeredRectangleGeneralGrowthBoundary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:41.321607+00:00
-- url     : https://prove2.me/theorems/9a35c2c2-7e6e-489e-91fb-79e5f355d5f5
-- title:
--   Locality: card centered Rectangle General Growth Boundary le
-- statement:
--   The general rectangle boundary has a concrete finite cardinality bound.
--   The extra `48 * threshold^2` relative to simultaneous growth is the explicit
--   short-range exterior collar, so no crossing interaction is silently dropped.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1251-L1337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1251-L1337

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

theorem QEC.Locality.card_centeredRectangleGeneralGrowthBoundary_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hThreshold : 1 ≤ threshold)
    (hOuterHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hOuterVertical : 1 ≤ 2 * outerVerticalRadius)
    (hHorizontalInset : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInset : outerVerticalRadius - threshold ≤ innerVerticalRadius) :
    ((centeredRectangleGeneralGrowthBoundary P embedding center
      innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold).selected.card : ℝ) ≤
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          innerHorizontalRadius innerVerticalRadius,
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by sorry
