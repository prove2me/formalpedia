-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_rational_S
-- name    : QEC.Coding.TannerLiftedProduct.lpsTheta_rational_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:23:20.949366+00:00
-- url     : https://prove2.me/theorems/da3faa14-8efd-4408-a32e-c996463ad7b7
-- title:
--   Tanner Lifted Product: lps Theta rational S
-- statement:
--   Exact finite characteristic/Gauss expansion at a rational translate of S.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L148-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L148-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.lpsTheta_rational_S (a : ℤ) (c : ℕ) [NeZero c] (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (-1/z+2*(a:ℂ)/(c:ℂ))=
      ((-Complex.I*z)^(1/2:ℂ)/(c:ℂ)) *
        ∑ r : Fin c, lpsQuadraticPhase a c r * jacobiTheta₂ ((r.val:ℂ)/(c:ℂ)) (z/(c:ℂ)^2) := by sorry
