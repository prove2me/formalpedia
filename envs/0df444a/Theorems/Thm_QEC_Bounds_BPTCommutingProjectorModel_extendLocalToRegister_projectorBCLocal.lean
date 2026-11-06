-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_projectorBCLocal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorBCLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:01.601942+00:00
-- url     : https://prove2.me/theorems/033c963f-5d62-4730-bd59-cad4778651f0
-- title:
--   BPTCommuting Projector Model: extend Local To Register projector BCLocal
-- statement:
--   The chosen `BC` representative extends back to the actual source product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2310-L2314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2310-L2314

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorBCLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).extendLocalToRegister (M.projectorBCLocal region) =
      M.projectorBC region := by sorry
