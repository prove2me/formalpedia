-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryLocalUnitaryToRegister_supported
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryLocalUnitaryToRegister_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:03.041136+00:00
-- url     : https://prove2.me/theorems/2cec4c7a-0e86-4120-a3b2-64213e562fd6
-- title:
--   BPTCommuting Projector Model: boundary Local Unitary To Register supported
-- statement:
--   The lifted boundary unitary is physically supported on the boundary sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1665-L1674
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1665-L1674

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryLocalUnitaryToRegister_supported
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    M.UnitarySupportedOn (M.boundary region)
      (M.boundaryLocalUnitaryToRegister region U) := by sorry
