-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_region_sector_dichotomy
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_region_sector_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:28:21.140773+00:00
-- url     : https://prove2.me/theorems/767040fa-3230-4daa-9039-0f2c0f936ef3
-- title:
--   BPTCommuting Projector Model: second Cut region sector dichotomy
-- statement:
--   Region correctability collapses each physical internal-boundary sector in the
--   second `AB / B bar(M)` BV03 cut to zero or the full code projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L572-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L572-L589

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_region_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    M.fullCodeProjector * M.secondCutPhysicalSectorProjector region component = 0 ∨
    M.fullCodeProjector * M.secondCutPhysicalSectorProjector region component =
      M.fullCodeProjector := by sorry
