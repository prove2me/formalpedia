-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Difference_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2Difference_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:41.135322+00:00
-- url     : https://prove2.me/theorems/f2f30e77-d986-4624-b991-205e71da844c
-- title:
--   Tanner Lifted Product: lps E2 Difference has Sum
-- statement:
--   The genuine convergent E2 series and its dilated reindexing give the actual difference series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L248-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L248-L261

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2Difference_hasSum (m : ℕ) (hm : 0 < m) (z : ℍ) :
    HasSum (fun n : ℕ => lpsE2DifferenceCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsE2Difference m hm z) := by sorry
