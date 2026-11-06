-- Prove2me | Theorems.Thm_QEC_Locality_card_centeredRectangleShellStrip_two_le
-- name    : QEC.Locality.card_centeredRectangleShellStrip_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:43.394326+00:00
-- url     : https://prove2.me/theorems/6eb6e987-08d8-47b2-ba25-e448222540e0
-- title:
--   Locality: card centered Rectangle Shell Strip two le
-- statement:
--   The Locality construction uses the card centered Rectangle Shell Strip two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L724-L739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L724-L739

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

theorem QEC.Locality.card_centeredRectangleShellStrip_two_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius) :
    ((centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold 2).card : ℝ) ≤ 12 * outerHorizontalRadius * threshold := by sorry
