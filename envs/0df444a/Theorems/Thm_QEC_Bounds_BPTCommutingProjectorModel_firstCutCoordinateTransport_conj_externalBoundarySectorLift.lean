-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_externalBoundarySectorLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_externalBoundarySectorLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:26:32.765747+00:00
-- url     : https://prove2.me/theorems/e8de01d9-4f17-4d27-a1d6-5a0f576204f4
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj external Boundary Sector Lift
-- statement:
--   The first-cut associators carry the virtual `C` sector lift to the same
--   `A,B,C,D` operator exposed by the external-boundary transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3643-L3666
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3643-L3666

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_externalBoundarySectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map
          (1 : Semantics.Operator
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))) ) := by sorry
