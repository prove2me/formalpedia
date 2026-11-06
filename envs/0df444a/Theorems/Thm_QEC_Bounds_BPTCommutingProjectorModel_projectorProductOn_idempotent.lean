-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProductOn_idempotent
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:35.459064+00:00
-- url     : https://prove2.me/theorems/5a034f5e-6553-4108-90f0-4194d6a31563
-- title:
--   BPTCommuting Projector Model: projector Product On idempotent
-- statement:
--   A finite selected product of commuting idempotent BPT projectors is idempotent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2058-L2107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2058-L2107

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_idempotent (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (M.projectorProductOn checks).comp (M.projectorProductOn checks) =
      M.projectorProductOn checks := by sorry
