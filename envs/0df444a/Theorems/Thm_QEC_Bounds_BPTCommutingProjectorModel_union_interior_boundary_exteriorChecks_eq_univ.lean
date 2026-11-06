-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_union_interior_boundary_exteriorChecks_eq_univ
-- name    : QEC.Bounds.BPTCommutingProjectorModel.union_interior_boundary_exteriorChecks_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:57.353202+00:00
-- url     : https://prove2.me/theorems/f419d8a1-27b1-494d-88fb-58a82c3a846b
-- title:
--   BPTCommuting Projector Model: union interior boundary exterior Checks eq univ
-- statement:
--   The three source check families partition the full finite projector family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1990-L2004
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1990-L2004

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

theorem QEC.Bounds.BPTCommutingProjectorModel.union_interior_boundary_exteriorChecks_eq_univ
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.interiorChecks region ∪ M.boundaryChecks region) ∪ M.exteriorChecks region = Finset.univ := by sorry
