-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_of_measurementDistance_card_lt
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_measurementDistance_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:09.826336+00:00
-- url     : https://prove2.me/theorems/b689f1cf-e1ed-44a7-909c-1cd2f13dc8aa
-- title:
--   BPTCommuting Projector Model: region Erasure Recoverable of measurement Distance card lt
-- statement:
--   The #402 BPT measurement-distance convention yields a concrete CPTP erasure
--   recovery for every finite region strictly below that distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2034-L2044
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2034-L2044

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_measurementDistance_card_lt
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (region : Finset L.Site) (hcard : region.card < distance) :
    M.RegionErasureRecoverable region := by sorry
