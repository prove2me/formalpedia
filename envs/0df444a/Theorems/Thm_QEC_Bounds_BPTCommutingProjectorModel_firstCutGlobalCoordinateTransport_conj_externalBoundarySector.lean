-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_externalBoundarySector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutGlobalCoordinateTransport_conj_externalBoundarySector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:15.665141+00:00
-- url     : https://prove2.me/theorems/3b35d33c-531f-414f-82aa-98b8fad3ecd3
-- title:
--   BPTCommuting Projector Model: first Cut Global Coordinate Transport conj external Boundary Sector
-- statement:
--   Physical external-boundary sector measurement in global first-cut coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4197-L4216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4197-L4216

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutGlobalCoordinateTransport_conj_externalBoundarySector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    (M.firstCutGlobalCoordinateTransport region).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
          (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))) =
      M.firstCutSectorLift region component := by sorry
