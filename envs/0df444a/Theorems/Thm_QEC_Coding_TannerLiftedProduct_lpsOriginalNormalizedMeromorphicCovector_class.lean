-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedMeromorphicCovector_class
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedMeromorphicCovector_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:50:45.022541+00:00
-- url     : https://prove2.me/theorems/02a52298-e33a-4e34-9873-61a4871285fa
-- title:
--   Tanner Lifted Product: lps Original Normalized Meromorphic Covector class
-- statement:
--   Repair preserves the genuine meromorphic quotient class, without asserting pointwise equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean#L129-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean#L129-L146

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedMeromorphicCovector_class
    (sigma : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :
    lpsOriginalCompactMeromorphicCovectorClass N hN sigma =
      lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalNormalizedMeromorphicCovectorRepresentative N hN sigma) := by sorry
