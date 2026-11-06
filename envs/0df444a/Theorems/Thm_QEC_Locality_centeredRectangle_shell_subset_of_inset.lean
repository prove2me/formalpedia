-- Prove2me | Theorems.Thm_QEC_Locality_centeredRectangle_shell_subset_of_inset
-- name    : QEC.Locality.centeredRectangle_shell_subset_of_inset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:15.718726+00:00
-- url     : https://prove2.me/theorems/6c6e2ca0-bebc-4943-aa1a-0b66ebda5505
-- title:
--   Locality: centered Rectangle shell subset of inset
-- statement:
--   A point in the target rectangle but outside an inner rectangle that is at
--   most one threshold inset lies in the standard target shell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1102-L1118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1102-L1118

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

theorem QEC.Locality.centeredRectangle_shell_subset_of_inset
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hHorizontalInner : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInner : outerVerticalRadius - threshold ≤ innerVerticalRadius) :
    centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius ⊆
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold) := by sorry
