-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_symm_conj_internalBoundaryLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_symm_conj_internalBoundaryLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:17:25.369339+00:00
-- url     : https://prove2.me/theorems/78d2558b-4683-45be-b408-9bab8fa6712b
-- title:
--   BPTCommuting Projector Model: second Cut Coordinate Transport symm conj internal Boundary Lift
-- statement:
--   Returning the physical internal-boundary lift through the second-cut
--   associator gives the exact `AB / B bar(M)` sector lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L194-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L194-L223

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_symm_conj_internalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.secondCutCoordinateTransport region).symm.conjOperator
      ((M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) =
      overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z) := by sorry
