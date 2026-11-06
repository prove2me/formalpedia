-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_externalBoundary_sector_dichotomy
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_externalBoundary_sector_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:26:33.562001+00:00
-- url     : https://prove2.me/theorems/b157146b-6527-4074-87e6-47922f655165
-- title:
--   BPTCommuting Projector Model: first Cut external Boundary sector dichotomy
-- statement:
--   External-boundary correctability collapses every first-cut isotypic sector to
--   either the zero code sector or the entire code.  The measured sector is
--   presented to no-information as an actual operator supported on
--   `partialPlus M`, then transported back to the virtual first-cut `C` factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3818-L3961
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3818-L3961

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
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_externalBoundary_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    M.fullCodeProjector *
        (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)) = 0 ∨
    M.fullCodeProjector *
        (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)) =
      M.fullCodeProjector := by sorry
