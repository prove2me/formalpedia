-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_factor_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2_slash_factor_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:07.35783+00:00
-- url     : https://prove2.me/theorems/fd6ed808-c8ac-4edc-881f-dac56a326c3f
-- title:
--   Tanner Lifted Product: lps E2 slash factor tendsto
-- statement:
--   An actual integral and upper-triangular matrix product gives its genuine E2 slash constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L100-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L100-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2_slash_factor_tendsto (δ : SL(2,ℤ)) (h : GL (Fin 2) ℝ)
    (hc : h 1 0=0) (hd : 0<h.det.val) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ*h))
      UpperHalfPlane.atImInfty (𝓝 ((h.det.val:ℂ)*(h 1 1:ℂ)^(-(2:ℤ)))) := by sorry
