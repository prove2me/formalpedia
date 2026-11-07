-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceModularForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2DifferenceModularForm_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:26:24.952197+00:00
-- url     : https://prove2.me/theorems/53018f97-3b2e-4cf8-ae70-8cd669c0ee46
-- title:
--   Tanner Lifted Product: lps E2 Difference Modular Form apply
-- statement:
--   The constructed modular form keeps the actual E2-difference function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L188-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L188-L189

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2DifferenceModularForm_apply (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsE2DifferenceModularForm m hm z=lpsE2Difference m hm z := by sorry
