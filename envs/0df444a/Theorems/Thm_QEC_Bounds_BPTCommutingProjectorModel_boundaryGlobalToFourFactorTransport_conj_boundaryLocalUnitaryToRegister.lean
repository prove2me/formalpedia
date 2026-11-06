-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:14.231503+00:00
-- url     : https://prove2.me/theorems/e67f00ae-1b31-4676-bfb7-21cbe52fb757
-- title:
--   BPTCommuting Projector Model: boundary Global To Four Factor Transport conj boundary Local Unitary To Register
-- statement:
--   The physical boundary lift is exactly the corresponding `BC` action in the
--   boundary-based four-factor coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1680-L1693
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1680-L1693

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToFourFactorTransport region).conjOperator
        (M.boundaryLocalUnitaryToRegister region U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator U.toLinearEquiv.toLinearMap) := by sorry
