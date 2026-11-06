-- Prove2me | Theorems.Thm_QEC_Locality_card_centeredRectangleShellStrip_one_le
-- name    : QEC.Locality.card_centeredRectangleShellStrip_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:41.880576+00:00
-- url     : https://prove2.me/theorems/b7dbae8f-0f0a-43bd-8dd9-e443882bcf83
-- title:
--   Locality: card centered Rectangle Shell Strip one le
-- statement:
--   The Locality construction uses the card centered Rectangle Shell Strip one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L706-L721
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L706-L721

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

theorem QEC.Locality.card_centeredRectangleShellStrip_one_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold 1).card : ℝ) ≤ 12 * outerVerticalRadius * threshold := by sorry
