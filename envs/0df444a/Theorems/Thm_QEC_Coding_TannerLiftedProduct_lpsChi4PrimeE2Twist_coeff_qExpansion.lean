-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_coeff_qExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_coeff_qExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:28.065028+00:00
-- url     : https://prove2.me/theorems/b7c745a4-24ca-4063-873a-3db302c2905d
-- title:
--   Tanner Lifted Product: lps Chi4 Prime E2 Twist coeff q Expansion
-- statement:
--   True analytic uniqueness computes every actual coefficient with both quadratic-character factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L141-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L141-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_coeff_qExpansion (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2Twist q))=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4) := by sorry
