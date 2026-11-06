-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_internalBoundary_disjoint_exterior
-- name    : QEC.Bounds.BPTCommutingProjectorModel.internalBoundary_disjoint_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:32.056274+00:00
-- url     : https://prove2.me/theorems/0a1abcde-37bc-40a7-80d0-633e837ed531
-- title:
--   BPTCommuting Projector Model: internal Boundary disjoint exterior
-- statement:
--   The internal boundary and source exterior are disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L383-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L383-L389

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.internalBoundary_disjoint_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.internalBoundary region) (M.exterior region) := by sorry
