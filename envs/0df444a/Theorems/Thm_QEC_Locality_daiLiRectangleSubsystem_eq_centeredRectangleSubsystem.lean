-- Prove2me | Theorems.Thm_QEC_Locality_daiLiRectangleSubsystem_eq_centeredRectangleSubsystem
-- name    : QEC.Locality.daiLiRectangleSubsystem_eq_centeredRectangleSubsystem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:23.412296+00:00
-- url     : https://prove2.me/theorems/eb7d5dc8-21e9-4e79-a4ed-3a5f45db7f2b
-- title:
--   Locality: dai Li Rectangle Subsystem eq centered Rectangle Subsystem
-- statement:
--   The concrete #496 rectangle and the centered-growth rectangle are the
--   same finite subsystem, including all dependent erasure data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2031-L2038
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2031-L2038

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

theorem QEC.Locality.daiLiRectangleSubsystem_eq_centeredRectangleSubsystem
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ) :
    daiLiRectangleSubsystem embedding lower upper =
      centeredRectangleSubsystem embedding (daiLiRectangleCenter lower upper)
        (daiLiRectangleHorizontalRadius lower upper)
        (daiLiRectangleVerticalRadius lower upper) := by sorry
