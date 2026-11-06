-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_source_overlap_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_source_overlap_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:14.905499+00:00
-- url     : https://prove2.me/theorems/23d866cc-e0f6-4fd4-8cce-1fd29bd9d701
-- title:
--   BPTCommuting Projector Model: second Cut Coordinate Transport conj source overlap product
-- statement:
--   The second `AB / B bar(M)` overlap product is the full BPT code projector
--   after the explicit second-cut coordinate transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L261-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L261-L291

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_source_overlap_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (M.secondCutCodeLift region) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by sorry
