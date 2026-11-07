-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2ShiftAtPrimeCusp_tendsto_of_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2ShiftAtPrimeCusp_tendsto_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:36.188551+00:00
-- url     : https://prove2.me/theorems/451764d5-79aa-4c96-9d20-f048288137fc
-- title:
--   Tanner Lifted Product: lps E2 Shift At Prime Cusp tendsto of column
-- statement:
--   The actual factorization proves the translated E2 cusp limit from arithmetic column data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L179-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L179-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2ShiftAtPrimeCusp_tendsto_of_column (q : ℕ) [NeZero q] (r : ℤ)
    (g : ℝ) (hg : g≠0) (δ : SL(2,ℤ))
    (ha : (δ 0 0:ℝ)*g=(r:ℝ)+1) (hc : (δ 1 0:ℝ)*g=(q:ℝ)) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ z))
      ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) UpperHalfPlane.atImInfty (𝓝 ((g:ℂ)^2)) := by sorry
