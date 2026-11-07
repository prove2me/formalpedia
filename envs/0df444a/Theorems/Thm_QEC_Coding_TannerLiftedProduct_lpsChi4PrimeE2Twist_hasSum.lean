-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:21.794784+00:00
-- url     : https://prove2.me/theorems/76b59ad3-6d9a-4cff-9500-e9614ac17bf2
-- title:
--   Tanner Lifted Product: lps Chi4 Prime E2 Twist has Sum
-- statement:
--   The genuine quarter-translated series and full chi4 Fourier transform prove the iterated convergent divisor series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L53-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L53-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_hasSum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
      lpsChi4E2Character (n:ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsChi4PrimeE2Twist q z) := by sorry
