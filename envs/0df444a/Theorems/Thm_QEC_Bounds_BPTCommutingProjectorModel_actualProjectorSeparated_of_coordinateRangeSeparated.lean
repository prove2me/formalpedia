-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_of_coordinateRangeSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_of_coordinateRangeSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:18:45.902457+00:00
-- url     : https://prove2.me/theorems/774782f8-918f-4eac-bbff-673882e58d5c
-- title:
--   BPTCommuting Projector Model: actual Projector Separated of coordinate Range Separated
-- statement:
--   The #378 support-square locality condition turns an explicit coordinate gap
--   into the actual-projector separation premise of #403.  No graph proxy or
--   assumed union recovery is involved.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1454-L1466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1454-L1466

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

theorem QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_of_coordinateRangeSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hgap : L.lattice.CoordinateRangeSeparated M.interactionRange left right) :
    M.ActualProjectorSeparated left right := by sorry
