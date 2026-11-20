-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_comm
-- name    : QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:31:10.990737+00:00
-- url     : https://prove2.me/theorems/f00fd677-f13b-4a5b-aea4-3c906bdf347c
-- title:
--   BPTCommuting Projector Model: actual Projector Separated comm
-- statement:
--   Actual-projector separation is symmetric in its two regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L31-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L31-L39

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

theorem QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_comm
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site) :
    M.ActualProjectorSeparated left right ↔
      M.ActualProjectorSeparated right left := by sorry
