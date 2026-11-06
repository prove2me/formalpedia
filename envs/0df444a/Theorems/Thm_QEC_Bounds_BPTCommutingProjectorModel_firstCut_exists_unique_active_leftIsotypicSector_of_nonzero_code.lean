-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:20:12.205208+00:00
-- url     : https://prove2.me/theorems/ca826da2-f5f7-4c31-b93d-c4f73a8ba09d
-- title:
--   BPTCommuting Projector Model: first Cut exists unique active left Isotypic Sector of nonzero code
-- statement:
--   For a nonempty code, external-boundary correctability leaves exactly one
--   first-cut left-isotypic sector active.  The proof calls the generic finite
--   sector-collapse theorem on a nonzero double coefficient of the actual full
--   first-cut code projector, then promotes that coefficient conclusion back to
--   the full projector using the physical-sector dichotomy above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4451-L4551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4451-L4551

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.firstCutProjectorMC region))
        (M.fourFactorC region),
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          M.firstCutCodeLift region ∧
        ∀ other : isotypicComponents
            (leftInteractionAlgebra (M.firstCutProjectorMC region))
            (M.fourFactorC region),
          other ≠ component →
          M.firstCutCodeLift region * M.firstCutSectorLift region other = 0 := by sorry
