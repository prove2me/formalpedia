-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_supportCouples_sdiff_right_iff_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.supportCouples_sdiff_right_iff_of_actualProjectorSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:48.077977+00:00
-- url     : https://prove2.me/theorems/254a3a24-ac2e-4f47-a645-0bcb99823837
-- title:
--   BPTCommuting Projector Model: support Couples sdiff right iff of actual Projector Separated
-- statement:
--   Removing the overlap from the left region changes neither side of a projector's
--   source coupling test: actual separation says no projector can see a removed
--   site.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L58-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L58-L92

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

theorem QEC.Bounds.BPTCommutingProjectorModel.supportCouples_sdiff_right_iff_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) (check : kappa) :
    M.supportCouples check (left \ right) ↔ M.supportCouples check left := by sorry
