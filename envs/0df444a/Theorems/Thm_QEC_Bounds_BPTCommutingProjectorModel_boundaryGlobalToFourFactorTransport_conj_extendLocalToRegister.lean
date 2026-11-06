-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:17.400843+00:00
-- url     : https://prove2.me/theorems/b0967bab-3e12-4ae4-a4bc-c38cf2d68ea1
-- title:
--   BPTCommuting Projector Model: boundary Global To Four Factor Transport conj extend Local To Register
-- statement:
--   The boundary-based full four-factor route has the exact `BC` support equation
--   for every boundary-local operator.  The later equality of coordinate routes
--   will transfer this statement to `fourFactorTransport` itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1642-L1652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1642-L1652

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToFourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.boundary region)).extendLocalToRegister P) =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator P) := by sorry
