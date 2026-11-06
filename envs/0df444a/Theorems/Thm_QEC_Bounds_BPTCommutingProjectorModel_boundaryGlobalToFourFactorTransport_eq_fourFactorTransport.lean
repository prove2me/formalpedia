-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:35.670207+00:00
-- url     : https://prove2.me/theorems/5ba7fc5d-83a2-4c83-9ff1-06095015a5a7
-- title:
--   BPTCommuting Projector Model: boundary Global To Four Factor Transport eq four Factor Transport
-- statement:
--   The boundary-based full transport is exactly the canonical four-factor transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1573-L1580
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1573-L1580

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.boundaryGlobalToFourFactorTransport region = M.fourFactorTransport region := by sorry
