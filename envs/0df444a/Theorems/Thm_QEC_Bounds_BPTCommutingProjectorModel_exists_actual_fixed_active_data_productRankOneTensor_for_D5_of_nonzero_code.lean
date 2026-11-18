-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-17T23:55:24.121793+00:00
-- url     : https://prove2.me/theorems/570f8b11-7043-43b4-8827-a6054cf7305f
-- title:
--   BPTCommuting Projector Model: exists actual fixed active data product Rank One Tensor for D5 of nonzero code
-- statement:
--   Choose one actual common-factor witness package and retain it through the
--   fixed-witness D2 product block.  The final nested proposition is the stronger
--   fixed-data theorem above, so its `phi`, joint compression, reconstruction, and
--   D1 product equation all remain attached to these exact sector witnesses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActualProduct.lean#L37-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActualProduct.lean#L37-L52

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Product
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActualProductData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActualProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_actual_fixed_active_data_productRankOneTensor_for_D5_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    M.ActualFixedActiveDataProductRankOneTensor region := by sorry
