-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:44.715196+00:00
-- url     : https://prove2.me/theorems/d8b5c87c-e364-403f-9d2b-05ca2b6569d6
-- title:
--   BPTCommuting Projector Model: boundary Complement To ADTransport apply boundary Complement To ADBasis Vector
-- statement:
--   The complementary boundary transport has the compact named `A tensor D` basis output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1409-L1419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1409-L1419

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    (M.boundaryComplementToADTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).complementDimensions) Complex labels) =
      M.boundaryComplementToADBasisVector region labels := by sorry
