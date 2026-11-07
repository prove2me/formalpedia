-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_level_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_level_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:07:50.247869+00:00
-- url     : https://prove2.me/theorems/f785d7ec-2f0d-4c87-ae17-ab41ed2250e4
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field level le
-- statement:
--   Actual level inclusion for the same original generated complex function fields.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L86-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullFieldLevelPullback.lean#L86-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_level_le
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hposN ≤ lpsOriginalGeneratedFunctionField M hposM := by sorry
