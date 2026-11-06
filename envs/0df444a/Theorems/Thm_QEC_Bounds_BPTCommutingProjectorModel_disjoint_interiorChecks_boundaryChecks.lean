-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disjoint_interiorChecks_boundaryChecks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorChecks_boundaryChecks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:59.141619+00:00
-- url     : https://prove2.me/theorems/ef1fc6b5-b6c7-48eb-93e2-0ba663625f9c
-- title:
--   BPTCommuting Projector Model: disjoint interior Checks boundary Checks
-- statement:
--   The `AB` source check family is disjoint from the middle `BC` family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2199-L2204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2199-L2204

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

theorem QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorChecks_boundaryChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region) (M.boundaryChecks region) := by sorry
