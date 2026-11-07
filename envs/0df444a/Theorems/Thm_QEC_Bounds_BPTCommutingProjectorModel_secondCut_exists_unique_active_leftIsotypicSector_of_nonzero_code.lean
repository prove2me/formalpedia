-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:24.040054+00:00
-- url     : https://prove2.me/theorems/0bba36a5-cbb6-4f2a-ad62-2423ac420cdf
-- title:
--   BPTCommuting Projector Model: second Cut exists unique active left Isotypic Sector of nonzero code
-- statement:
--   For a nonempty code, region correctability leaves exactly one second-cut
--   left-isotypic sector active in the actual `AB / B bar(M)` overlap product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L759-L861
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L759-L861

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region) :
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
