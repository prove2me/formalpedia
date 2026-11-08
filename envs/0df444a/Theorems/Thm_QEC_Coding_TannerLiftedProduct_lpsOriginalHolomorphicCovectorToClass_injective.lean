-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicCovectorToClass_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectorToClass_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:49:25.081217+00:00
-- url     : https://prove2.me/theorems/c204eb6c-7abd-4d80-af94-0ef7b3117c21
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Covector To Class injective
-- statement:
--   Actual local germ equality determines an analytic section, so the native quotient map is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicNativeCovectors.lean#L69-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicNativeCovectors.lean#L69-L89

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicNativeCovectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectorToClass_injective :
    Function.Injective (lpsOriginalHolomorphicCovectorToClassLinearMap N hN) := by sorry
