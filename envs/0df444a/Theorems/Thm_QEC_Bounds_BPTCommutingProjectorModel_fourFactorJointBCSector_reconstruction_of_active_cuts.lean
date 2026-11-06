-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSector_reconstruction_of_active_cuts
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSector_reconstruction_of_active_cuts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:34:53.825508+00:00
-- url     : https://prove2.me/theorems/7b2ba82a-fc98-486d-a846-fd073b1c525b
-- title:
--   BPTCommuting Projector Model: four Factor Joint BCSector reconstruction of active cuts
-- statement:
--   For fixed active BPT components, the two retained cut-absorption equations
--   give the four-factor reconstruction through their common simultaneous-sector
--   compression.  This is the D5 reconstruction bridge; it does not select new
--   components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L340-L426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L340-L426

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSector_reconstruction_of_active_cuts
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hCactive : M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent =
      M.firstCutCodeLift region)
    (hBactive : M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent =
      M.secondCutCodeLift region) :
    let pB := bcomponent.1.restrictScalars Complex
    let pC := ccomponent.1.restrictScalars Complex
    let J := fourFactorJointBCSectorEmbedding
      (A := M.fourFactorA region) (D := M.fourFactorD region) pB pC
    let P4 := (M.fourFactorTransport region).conjOperator M.fullCodeProjector
    P4 = J.comp (((LinearMap.adjoint J).comp (P4.comp J)).comp (LinearMap.adjoint J)) := by sorry
