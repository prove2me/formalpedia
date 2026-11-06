-- Prove2me | Theorems.Thm_QEC_Locality_card_centeredRectangle_shell_le
-- name    : QEC.Locality.card_centeredRectangle_shell_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:26.442191+00:00
-- url     : https://prove2.me/theorems/84310963-26a8-4a77-9b78-11cb616b4e35
-- title:
--   Locality: card centered Rectangle shell le
-- statement:
--   The shell of a simultaneously grown rectangle has the perimeter-scale
--   packing bound needed by Dai--Li's growing-region argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L801-L836
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L801-L836

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

theorem QEC.Locality.card_centeredRectangle_shell_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold := by sorry
