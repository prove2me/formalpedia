-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_prime_cusp_not_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_prime_cusp_not_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:46.145107+00:00
-- url     : https://prove2.me/theorems/eeb03dfc-8bdb-4047-8a89-18f9f437cbfa
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist prime cusp not zero
-- statement:
--   The actual nonzero full-filter limit rejects vanishing at the rational cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L308-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L308-L313

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_prime_cusp_not_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ¬UpperHalfPlane.IsZeroAtImInfty
      (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) := by sorry
