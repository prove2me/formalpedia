-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_unique_active_leftIsotypicSector_or_disentangled
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_unique_active_leftIsotypicSector_or_disentangled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T15:03:18.305421+00:00
-- url     : https://prove2.me/theorems/50155432-6d41-4a03-bcee-b3aa0ff44ea2
-- title:
--   BPTCommuting Projector Model: second Cut unique active left Isotypic Sector or disentangled
-- statement:
--   The zero-code branch is already disentangled; otherwise the second cut has one active sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L864-L881
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L864-L881

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_unique_active_leftIsotypicSector_or_disentangled
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region) :
    M.Disentangled region ∨
      ∃ component : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        M.secondCutCodeLift region * M.secondCutSectorLift region component =
            M.secondCutCodeLift region ∧
          ∀ other : isotypicComponents
              (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
              (M.fourFactorB region),
            other ≠ component →
            M.secondCutCodeLift region * M.secondCutSectorLift region other = 0 := by sorry
