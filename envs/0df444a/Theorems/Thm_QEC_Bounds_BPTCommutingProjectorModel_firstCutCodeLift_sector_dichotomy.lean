-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_dichotomy
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:19:33.60921+00:00
-- url     : https://prove2.me/theorems/474b317c-4c81-4fdd-ac87-e35968e313c8
-- title:
--   BPTCommuting Projector Model: first Cut Code Lift sector dichotomy
-- statement:
--   The physical external-boundary dichotomy transported into first-cut
--   coordinates.  This is the exact `hsector` source for finite isotypic-sector
--   collapse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4224-L4262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4224-L4262

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    M.firstCutCodeLift region * M.firstCutSectorLift region component = 0 ∨
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
        M.firstCutCodeLift region := by sorry
