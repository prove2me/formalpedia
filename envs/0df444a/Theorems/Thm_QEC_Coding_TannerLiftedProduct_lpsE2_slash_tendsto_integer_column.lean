-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_tendsto_integer_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_integer_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:46.888879+00:00
-- url     : https://prove2.me/theorems/2e434fa7-6766-4e51-a9e5-80847fb5cca4
-- title:
--   Tanner Lifted Product: lps E2 slash tendsto integer column
-- statement:
--   Actual gcd reduction constructs the primitive column and its scale, proving the rational-column E2 limit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L95-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L95-L118

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_integer_column (M : GL (Fin 2) ℝ)
    (hd : 0<M.det.val) (a c : ℤ) (t : ℝ) (ht : t≠0)
    (ha : M 0 0=(a:ℝ)/t) (hc : M 1 0=(c:ℝ)/t)
    (hpos : 0<Int.gcd a c) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] M) UpperHalfPlane.atImInfty
      (𝓝 ((((Int.gcd a c:ℕ):ℂ)/(t:ℂ))^2/(M.det.val:ℂ))) := by sorry
