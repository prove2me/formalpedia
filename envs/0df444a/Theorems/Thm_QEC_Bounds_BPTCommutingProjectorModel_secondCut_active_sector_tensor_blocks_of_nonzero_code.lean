-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_active_sector_tensor_blocks_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_active_sector_tensor_blocks_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T15:03:15.859911+00:00
-- url     : https://prove2.me/theorems/3449fcd5-933a-436b-9863-fecd7753b41a
-- title:
--   BPTCommuting Projector Model: second Cut active sector tensor blocks of nonzero code
-- statement:
--   The unique hM-active second-cut sector carries the actual BV03 tensor-block
--   projector equalities.  This consumes the isotypic polar unitary rather than
--   recording a desired factorization as data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L889-L922
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L889-L922

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_active_sector_tensor_blocks_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
        (M.fourFactorB region),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region ∧
      (∀ other : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        other ≠ component →
        M.secondCutCodeLift region * M.secondCutSectorLift region other = 0) ∧
      OverlapProjectorTensorBlockFactorization
        (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component := by sorry
