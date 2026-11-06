-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_actual_commonFactorization_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_actual_commonFactorization_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T19:55:00.447052+00:00
-- url     : https://prove2.me/theorems/d1e8b02c-f202-46e6-9828-0ca561b22be1
-- title:
--   BPTCommuting Projector Model: exists actual common Factorization of nonzero code
-- statement:
--   The source common factor is obtained from the two physical BV03 blocks, not
--   from caller-supplied sequential equalities.  The first-cut complement block
--   `P_D` remains an unconstrained projection throughout this assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/CommonFactorization.lean#L153-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/CommonFactorization.lean#L153-L178

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Blocks
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_CommonFactorizationData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_CommonFactorizationNonzeroData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_CommonFactorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_actual_commonFactorization_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    ActualCommonFactorizationOfNonzeroCode M region := by sorry
