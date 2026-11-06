-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_active_sector_tensor_blocks_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_active_sector_tensor_blocks_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T15:02:27.855204+00:00
-- url     : https://prove2.me/theorems/8b65cc8e-8be1-4e80-b596-b7e9ef088986
-- title:
--   BPTCommuting Projector Model: first Cut active sector tensor blocks of nonzero code
-- statement:
--   The unique external-boundary-active first-cut sector carries the concrete BV03
--   tensor-block equations for `Pi_MC` and `Pi_CD`.  It is the `C = C' tensor C''`
--   half of the source factorization and is consumed jointly with the second cut
--   below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L53-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L53-L85

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_active_sector_tensor_blocks_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.firstCutProjectorMC region))
        (M.fourFactorC region),
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          M.firstCutCodeLift region ∧
      (∀ other : isotypicComponents
          (leftInteractionAlgebra (M.firstCutProjectorMC region))
          (M.fourFactorC region),
        other ≠ component →
        M.firstCutCodeLift region * M.firstCutSectorLift region other = 0) ∧
      OverlapProjectorTensorBlockFactorization
        (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) component := by sorry
