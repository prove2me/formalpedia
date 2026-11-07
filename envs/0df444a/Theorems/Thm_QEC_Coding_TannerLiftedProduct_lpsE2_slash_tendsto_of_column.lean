-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_tendsto_of_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:09.437354+00:00
-- url     : https://prove2.me/theorems/c634802f-b7f7-47bb-8b0c-4b41ab578869
-- title:
--   Tanner Lifted Product: lps E2 slash tendsto of column
-- statement:
--   The actual delta inverse times M is triangular with derived entries and determinant, giving the E2 cusp scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L37-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L37-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_of_column (M : GL (Fin 2) ℝ)
    (hd : 0<M.det.val) (δ : SL(2,ℤ)) (g : ℝ) (hg : g≠0)
    (ha : (δ 0 0:ℝ)*g=M 0 0) (hc : (δ 1 0:ℝ)*g=M 1 0) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] M) UpperHalfPlane.atImInfty
      (𝓝 ((g:ℂ)^2/(M.det.val:ℂ))) := by sorry
