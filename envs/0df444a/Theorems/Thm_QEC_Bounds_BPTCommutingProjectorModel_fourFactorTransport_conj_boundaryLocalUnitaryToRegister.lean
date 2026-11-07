-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_boundaryLocalUnitaryToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_boundaryLocalUnitaryToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:22.120532+00:00
-- url     : https://prove2.me/theorems/0bf0486a-d638-4a86-ad43-f6d0b97b597f
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj boundary Local Unitary To Register
-- statement:
--   The canonical four-factor route has the same exact physical-boundary lift equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1696-L1706
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1696-L1706

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_boundaryLocalUnitaryToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.fourFactorTransport region).conjOperator
        (M.boundaryLocalUnitaryToRegister region U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator U.toLinearEquiv.toLinearMap) := by sorry
