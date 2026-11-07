-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOpenPartialHomeomorph_inverse_deriv
-- name    : QEC.Coding.TannerLiftedProduct.lpsOpenPartialHomeomorph_inverse_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:45:50.69578+00:00
-- url     : https://prove2.me/theorems/18448d9c-9d68-4fe3-bd94-78432dea037f
-- title:
--   Tanner Lifted Product: lps Open Partial Homeomorph inverse deriv
-- statement:
--   The derivative of the actual inverse chart cancels the forward derivative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L16-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L16-L29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOpenPartialHomeomorph_inverse_deriv
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z∈e.source)
    (ha : AnalyticAt ℂ e z) (hd : deriv e z≠0) :
    deriv e.symm (e z) * deriv e z = 1 := by sorry
