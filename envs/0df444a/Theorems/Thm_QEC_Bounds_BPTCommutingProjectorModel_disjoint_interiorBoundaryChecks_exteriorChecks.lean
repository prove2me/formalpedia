-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disjoint_interiorBoundaryChecks_exteriorChecks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorBoundaryChecks_exteriorChecks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:57.686199+00:00
-- url     : https://prove2.me/theorems/f1549cc0-9dee-411a-ada6-b7e032366ef5
-- title:
--   BPTCommuting Projector Model: disjoint interior Boundary Checks exterior Checks
-- statement:
--   The combined `AB` and `BC` families are disjoint from the `CD` family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2207-L2215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2207-L2215

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

theorem QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorBoundaryChecks_exteriorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region ∪ M.boundaryChecks region) (M.exteriorChecks region) := by sorry
