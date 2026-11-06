-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_mul_CD_supportedOnRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_supportedOnRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:55:59.613848+00:00
-- url     : https://prove2.me/theorems/b50b70e3-f871-43de-a633-fa4724a7914e
-- title:
--   BPTCommuting Projector Model: projector BC mul CD supported On Register
-- statement:
--   The second source product `Pi_BC Pi_CD` acts only on `partial M union bar M`,
--   the `B bar(M)` side of the second BPT commuting-projector decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2461-L2467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2461-L2467

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_supportedOnRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region ∪ regionᶜ)).OperatorSupportedOnRegister
      (M.projectorBC region * M.projectorCD region) := by sorry
