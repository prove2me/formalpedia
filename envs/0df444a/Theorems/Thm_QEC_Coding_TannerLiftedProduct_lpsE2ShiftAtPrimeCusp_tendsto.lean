-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2ShiftAtPrimeCusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2ShiftAtPrimeCusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:30.875821+00:00
-- url     : https://prove2.me/theorems/d5489e08-c699-4047-8310-864b75241f26
-- title:
--   Tanner Lifted Product: lps E2 Shift At Prime Cusp tendsto
-- statement:
--   Actual Bezout and exceptional-column matrices prove every translated residue cusp constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L205-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L205-L232

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2ShiftAtPrimeCusp_tendsto (q : ℕ) [Fact q.Prime] (r : Fin q) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ z))
      ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) UpperHalfPlane.atImInfty
        (𝓝 (if r.val+1=q then (q:ℂ)^2 else 1)) := by sorry
