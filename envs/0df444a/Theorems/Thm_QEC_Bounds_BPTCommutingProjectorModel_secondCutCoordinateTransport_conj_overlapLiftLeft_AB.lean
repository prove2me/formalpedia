-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_overlapLiftLeft_AB
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_overlapLiftLeft_AB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:17:01.491011+00:00
-- url     : https://prove2.me/theorems/45943b5d-9a5d-4c6f-888c-e5eb36094154
-- title:
--   BPTCommuting Projector Model: second Cut Coordinate Transport conj overlap Lift Left AB
-- statement:
--   The second-cut associator sends the literal `AB` lift to the source `AB` factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L155-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L155-L164

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_overlapLiftLeft_AB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) P) =
      M.fourFactorExtendAB region P := by sorry
