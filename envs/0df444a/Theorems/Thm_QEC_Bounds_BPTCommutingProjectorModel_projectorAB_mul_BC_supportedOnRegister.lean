-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_supportedOnRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_supportedOnRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:54:17.620264+00:00
-- url     : https://prove2.me/theorems/a56b8e93-437f-49c9-9b63-2cc1f3a2d2ad
-- title:
--   BPTCommuting Projector Model: projector AB mul BC supported On Register
-- statement:
--   The first source product `Pi_AB Pi_BC` acts only on `M union partial M`, the
--   `MC` side of the first commuting-projector decomposition in the BPT proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2449-L2455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2449-L2455

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_supportedOnRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (region ∪ M.boundary region)).OperatorSupportedOnRegister
      (M.projectorAB region * M.projectorBC region) := by sorry
