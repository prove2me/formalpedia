-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_eq_fourFactorTransportFromRegion
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_eq_fourFactorTransportFromRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:18.809494+00:00
-- url     : https://prove2.me/theorems/e0db1fe5-add7-494e-994c-9907e0c3d335
-- title:
--   BPTCommuting Projector Model: four Factor Transport eq four Factor Transport From Region
-- statement:
--   Both cumulative constructions are exactly the same four-factor unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L611-L622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L611-L622

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_eq_fourFactorTransportFromRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorTransport region = M.fourFactorTransportFromRegion region := by sorry
