-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_codiscrete
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_codiscrete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:43:57.976991+00:00
-- url     : https://prove2.me/theorems/d78ff33d-46d6-4c6d-a36c-c6ec6861dcad
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Covector codiscrete
-- statement:
--   Repair preserves the representative away from a discrete set, in the actual codiscrete filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean#L83-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean#L83-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_codiscrete
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma) :
    letI := lpsOriginalFilledTopology N
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
      sigma y = lpsOriginalNormalizedFilledCovector N hN sigma y := by sorry
