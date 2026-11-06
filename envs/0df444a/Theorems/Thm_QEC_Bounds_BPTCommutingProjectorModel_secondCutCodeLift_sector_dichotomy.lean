-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_dichotomy
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_sector_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:19:06.017433+00:00
-- url     : https://prove2.me/theorems/9ba2817d-a99e-42ab-939b-ee4c71d9e008
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift sector dichotomy
-- statement:
--   The hM-driven physical sector dichotomy transported into literal second-cut
--   coordinates.  This is the `hsector` input for the second BV03 collapse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L595-L645
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L595-L645

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    M.secondCutCodeLift region * M.secondCutSectorLift region component = 0 ∨
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
        M.secondCutCodeLift region := by sorry
