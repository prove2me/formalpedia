-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_last_upper
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_last_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:57.139247+00:00
-- url     : https://prove2.me/theorems/28d2b1a8-9aa6-482a-a369-2ee2ab8f95e5
-- title:
--   Locality: dai Li Physical Greedy Rectangles last upper
-- statement:
--   The last rectangle of a nonempty greedy subdivision ends at the declared
--   upper atomization endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L727-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L727-L773

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_last_upper
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell lower upper : ℝ) (d : Nat)
    (atoms : List (ℝ × ℝ))
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hNonempty : daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms ≠ []) :
    (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).getLast
      hNonempty |>.2.2 = upper := by sorry
