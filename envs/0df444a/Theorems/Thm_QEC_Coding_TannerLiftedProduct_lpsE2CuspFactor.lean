-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2CuspFactor
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2CuspFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:24.585498+00:00
-- url     : https://prove2.me/theorems/4933aa85-324e-4ee7-99c3-7f6a2184530a
-- title:
--   Tanner Lifted Product: lps E2 Cusp Factor
-- statement:
--   The constructed integral and real matrices factor the actual rational translated cusp action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L150-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L150-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2CuspFactor (q : ℕ) [NeZero q] (r : ℤ) (g : ℝ) (hg : g≠0)
    (δ : SL(2,ℤ)) (ha : (δ 0 0:ℝ)*g=(r:ℝ)+1) (hc : (δ 1 0:ℝ)*g=(q:ℝ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation ((r:ℝ)/(q:ℝ))) *
      Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2PrimeCuspMatrix q) =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsE2DiagonalTranslation g ((δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)) hg) := by sorry
