-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_unique_active_leftIsotypicSector_or_disentangled
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_unique_active_leftIsotypicSector_or_disentangled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:59:48.933718+00:00
-- url     : https://prove2.me/theorems/fd9b2e5a-b3e0-4f2f-b358-56a33a486542
-- title:
--   BPTCommuting Projector Model: first Cut unique active left Isotypic Sector or disentangled
-- statement:
--   The zero-code branch is discharged by the existing degenerate disentangling
--   theorem; otherwise the first BV03 decomposition has a unique active sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L27-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L27-L44

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_unique_active_leftIsotypicSector_or_disentangled
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    M.Disentangled region ∨
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
