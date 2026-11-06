-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_internalBoundarySectorLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_internalBoundarySectorLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:27:54.676945+00:00
-- url     : https://prove2.me/theorems/7d18f3b6-9a23-4e33-9ffd-23f8c5539a55
-- title:
--   BPTCommuting Projector Model: second Cut Coordinate Transport conj internal Boundary Sector Lift
-- statement:
--   The second-cut associator sends a virtual internal-boundary lift to `B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L167-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L167-L188

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_internalBoundarySectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by sorry
