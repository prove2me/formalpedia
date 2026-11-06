-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProductOn_adjoint_eq_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:31.391746+00:00
-- url     : https://prove2.me/theorems/f1502a2d-732d-4d99-bb89-d38764f1c1e3
-- title:
--   BPTCommuting Projector Model: projector Product On adjoint eq self
-- statement:
--   A finite selected product of commuting self-adjoint BPT projectors is self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2019-L2055
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2019-L2055

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_adjoint_eq_self (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    LinearMap.adjoint (M.projectorProductOn checks) = M.projectorProductOn checks := by sorry
