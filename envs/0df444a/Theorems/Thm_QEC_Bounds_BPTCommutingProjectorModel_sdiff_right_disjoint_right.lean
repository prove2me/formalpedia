-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sdiff_right_disjoint_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sdiff_right_disjoint_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:29.270778+00:00
-- url     : https://prove2.me/theorems/42ee14e1-c779-4577-aeca-1c5aff818e2c
-- title:
--   BPTCommuting Projector Model: sdiff right disjoint right
-- statement:
--   The normalized left region is literally disjoint from the right region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L149-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L149-L153

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.sdiff_right_disjoint_right (left right : Finset L.Site) :
    Disjoint (left \ right) right := by sorry
