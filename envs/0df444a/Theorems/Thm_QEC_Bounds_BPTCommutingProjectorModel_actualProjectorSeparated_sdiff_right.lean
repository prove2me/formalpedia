-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_sdiff_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_sdiff_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:13.381932+00:00
-- url     : https://prove2.me/theorems/db4cda87-7062-439d-ae25-0b883eab39c5
-- title:
--   BPTCommuting Projector Model: actual Projector Separated sdiff right
-- statement:
--   Actual source separation is stable when the left overlap is normalized away.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L156-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L156-L165

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

theorem QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_sdiff_right
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.ActualProjectorSeparated (left \ right) right := by sorry
