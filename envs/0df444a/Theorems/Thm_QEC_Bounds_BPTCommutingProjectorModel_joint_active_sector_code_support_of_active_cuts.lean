-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_joint_active_sector_code_support_of_active_cuts
-- name    : QEC.Bounds.BPTCommutingProjectorModel.joint_active_sector_code_support_of_active_cuts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:22:04.900953+00:00
-- url     : https://prove2.me/theorems/b09e3892-17fb-43e6-bffb-e3380473f3e7
-- title:
--   BPTCommuting Projector Model: joint active sector code support of active cuts
-- statement:
--   After the two correctability-driven sector collapses, the transported full
--   code is supported on the simultaneous active `B` and `C` sectors.  This is the
--   common four-factor support equation needed to compose the two BV03 block
--   coordinates into the source residual `B'' tensor C'` code; it is stronger than
--   merely exhibiting the two blocks separately.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L932-L1030
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L932-L1030

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
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.joint_active_sector_code_support_of_active_cuts
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
    (M.fourFactorTransport region).conjOperator M.fullCodeProjector *
        (M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
              (leftIsotypicSectorProjector
                (M.fourFactorProjectorABLocal region) bcomponent))) *
        (M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
            ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
              (leftIsotypicSectorProjector
                (M.firstCutProjectorMC region) ccomponent))) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by sorry
