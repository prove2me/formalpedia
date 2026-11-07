-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Dilated_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2Dilated_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:43.669649+00:00
-- url     : https://prove2.me/theorems/ded0ee08-979f-4ba5-8feb-24b6b4f2820f
-- title:
--   Tanner Lifted Product: lps E2 Dilated has Sum
-- statement:
--   Injective multiplication and zero off its range reindex the genuine convergent E2 series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L215-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L215-L241

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2Dilated_hasSum (m : ℕ) (hm : 0 < m) (z : ℍ) :
    HasSum (fun n : ℕ => lpsE2DilationCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n)
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by sorry
