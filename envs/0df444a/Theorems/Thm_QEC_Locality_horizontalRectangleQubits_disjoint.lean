-- Prove2me | Theorems.Thm_QEC_Locality_horizontalRectangleQubits_disjoint
-- name    : QEC.Locality.horizontalRectangleQubits_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:09.567909+00:00
-- url     : https://prove2.me/theorems/49c16f2f-4cd4-48c6-8408-5ebc20368bf0
-- title:
--   Locality: horizontal Rectangle Qubits disjoint
-- statement:
--   A horizontal cut is an actual disjoint subdivision of the parent rectangle's qubits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2064-L2076
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2064-L2076

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

theorem QEC.Locality.horizontalRectangleQubits_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) :
    Disjoint (lowerHorizontalRectangleQubits embedding lower upper cut)
      (upperHorizontalRectangleQubits embedding lower upper cut) := by sorry
