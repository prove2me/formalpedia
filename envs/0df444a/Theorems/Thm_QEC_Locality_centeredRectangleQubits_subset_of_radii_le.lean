-- Prove2me | Theorems.Thm_QEC_Locality_centeredRectangleQubits_subset_of_radii_le
-- name    : QEC.Locality.centeredRectangleQubits_subset_of_radii_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:50.643084+00:00
-- url     : https://prove2.me/theorems/a50299e2-b060-4558-aedc-6d5845428d92
-- title:
--   Locality: centered Rectangle Qubits subset of radii le
-- statement:
--   A centered rectangle with smaller half-sides selects a subsystem of the
--   corresponding larger rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L840-L853
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L840-L853

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

theorem QEC.Locality.centeredRectangleQubits_subset_of_radii_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    {innerHorizontalRadius outerHorizontalRadius innerVerticalRadius outerVerticalRadius : ℝ}
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius) :
    centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius ⊆
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius := by sorry
