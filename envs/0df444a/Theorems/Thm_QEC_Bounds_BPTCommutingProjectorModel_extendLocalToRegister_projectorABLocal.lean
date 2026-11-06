-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_projectorABLocal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorABLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:06.319137+00:00
-- url     : https://prove2.me/theorems/77eb644d-849c-4dd6-9cdb-da7efd0741e6
-- title:
--   BPTCommuting Projector Model: extend Local To Register projector ABLocal
-- statement:
--   The chosen `AB` representative extends back to the actual source product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2297-L2301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2297-L2301

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorABLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem region).extendLocalToRegister (M.projectorABLocal region) =
      M.projectorAB region := by sorry
