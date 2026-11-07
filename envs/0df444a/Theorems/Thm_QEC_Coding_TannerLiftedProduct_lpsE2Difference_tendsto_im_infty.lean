-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Difference_tendsto_im_infty
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2Difference_tendsto_im_infty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:27:22.199187+00:00
-- url     : https://prove2.me/theorems/68754187-45df-4b51-80c2-1408f14fa016
-- title:
--   Tanner Lifted Product: lps E2 Difference tendsto im infty
-- statement:
--   The actual full-filter infinity constant is one minus the dilation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L295-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L295-L304

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2Difference_tendsto_im_infty (m : ℕ) (hm : 0 < m) :
    Tendsto (lpsE2Difference m hm) UpperHalfPlane.atImInfty (𝓝 (1-(m:ℂ))) := by sorry
