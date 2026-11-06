-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_fullCodeProjector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutGlobalCoordinateTransport_conj_fullCodeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:15:58.417813+00:00
-- url     : https://prove2.me/theorems/c95159ba-df04-4fc6-ad41-755334dfb29d
-- title:
--   BPTCommuting Projector Model: first Cut Global Coordinate Transport conj full Code Projector
-- statement:
--   The global first-cut coordinates carry the full code projector to its overlap product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4176-L4194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4176-L4194

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutGlobalCoordinateTransport_conj_fullCodeProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.firstCutCodeLift region := by sorry
