-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Difference_coeff_qExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2Difference_coeff_qExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:58.950988+00:00
-- url     : https://prove2.me/theorems/bc356e1c-567c-4d5f-af64-54730ea071c7
-- title:
--   Tanner Lifted Product: lps E2 Difference coeff q Expansion
-- statement:
--   True periodicity, holomorphicity, boundedness and analytic uniqueness prove every actual coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L264-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L264-L278

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2Difference_coeff_qExpansion (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2Difference m hm))=
      lpsE2DifferenceCoefficient m n := by sorry
