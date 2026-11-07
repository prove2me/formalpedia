-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_prime_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_prime_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:54.798135+00:00
-- url     : https://prove2.me/theorems/43e89bf4-2fb0-46d5-943c-a3a03d398141
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist prime cusp tendsto
-- statement:
--   The genuine finite weighted limits compute the actual twist constant at one over q.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L265-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L265-L294

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_prime_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q)
      UpperHalfPlane.atImInfty (𝓝 (lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))) := by sorry
