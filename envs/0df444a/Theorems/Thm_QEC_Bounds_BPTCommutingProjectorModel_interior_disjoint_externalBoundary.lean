-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_interior_disjoint_externalBoundary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.interior_disjoint_externalBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:45:08.131624+00:00
-- url     : https://prove2.me/theorems/04f2f93a-3e85-4e44-8448-90e97e391b82
-- title:
--   BPTCommuting Projector Model: interior disjoint external Boundary
-- statement:
--   The source interior and external boundary are disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L374-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L374-L380

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

theorem QEC.Bounds.BPTCommutingProjectorModel.interior_disjoint_externalBoundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interior region) (M.externalBoundary region) := by sorry
