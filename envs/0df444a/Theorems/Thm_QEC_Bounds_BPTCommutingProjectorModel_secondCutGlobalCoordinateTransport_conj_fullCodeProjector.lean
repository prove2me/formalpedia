-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_fullCodeProjector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport_conj_fullCodeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:58.252224+00:00
-- url     : https://prove2.me/theorems/0c6b7f3d-3277-45d9-807f-17b8f4550fbc
-- title:
--   BPTCommuting Projector Model: second Cut Global Coordinate Transport conj full Code Projector
-- statement:
--   The global second-cut coordinates carry the full code projector to its overlap product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L294-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L294-L311

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport_conj_fullCodeProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region := by sorry
