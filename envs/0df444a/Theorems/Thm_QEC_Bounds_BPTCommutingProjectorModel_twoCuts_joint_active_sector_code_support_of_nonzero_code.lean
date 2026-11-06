-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_twoCuts_joint_active_sector_code_support_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.twoCuts_joint_active_sector_code_support_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T15:03:40.299261+00:00
-- url     : https://prove2.me/theorems/9c0e7fc2-2871-4b3e-98e7-c7ba1b605573
-- title:
--   BPTCommuting Projector Model: two Cuts joint active sector code support of nonzero code
-- statement:
--   The existential active-sector statement is the preceding fixed-witness
--   support transport applied to the components selected by correctability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L1036-L1072
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L1036-L1072

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

theorem QEC.Bounds.BPTCommutingProjectorModel.twoCuts_joint_active_sector_code_support_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ∃ ccomponent : isotypicComponents
        (leftInteractionAlgebra (M.firstCutProjectorMC region))
        (M.fourFactorC region),
      ∃ bcomponent : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
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
