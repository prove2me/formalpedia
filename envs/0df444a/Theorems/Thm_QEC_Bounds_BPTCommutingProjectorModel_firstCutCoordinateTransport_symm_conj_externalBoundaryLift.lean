-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_symm_conj_externalBoundaryLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_symm_conj_externalBoundaryLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:20.574409+00:00
-- url     : https://prove2.me/theorems/e7e82a50-9252-4368-a9d9-7dc86fda620d
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport symm conj external Boundary Lift
-- statement:
--   Transporting a physical external-boundary local operator into first-cut
--   coordinates gives precisely the lift of its virtual `C` representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3672-L3702
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3672-L3702

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_symm_conj_externalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.firstCutCoordinateTransport region).symm.conjOperator
      ((M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z))) =
      overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map
          (1 : Semantics.Operator
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z) := by sorry
