-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2_real_shift_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2_real_shift_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:29.211393+00:00
-- url     : https://prove2.me/theorems/233765f4-d790-44cf-978d-a5576ccdfb87
-- title:
--   Tanner Lifted Product: lps Quadratic E2 real shift has Sum
-- statement:
--   Actual quarter translation and the standard additive phase transform the genuine prime-character convergent series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L37-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L37-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2_real_shift_hasSum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : ℤ) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
      ZMod.stdAddChar (((a*(n:ℤ)):ℤ):ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsQuadraticE2Twist q (((a:ℝ)/4) +ᵥ z)) := by sorry
