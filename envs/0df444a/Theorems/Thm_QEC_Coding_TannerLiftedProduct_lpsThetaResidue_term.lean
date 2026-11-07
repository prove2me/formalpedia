-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaResidue_term
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaResidue_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:07.731413+00:00
-- url     : https://prove2.me/theorems/c98fd3d0-ea4b-4333-9870-8b6775909c82
-- title:
--   Tanner Lifted Product: lps Theta Residue term
-- statement:
--   The integer quotient contributes an integral exponential period.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L86-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L86-L99

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.lpsThetaResidue_term (a k : ℤ) (c : ℕ) [NeZero c] (r : Fin c) (z : ℂ) :
    Complex.exp ((Real.pi:ℂ)*Complex.I*((k:ℂ)*(c:ℂ)+(r.val:ℂ))^2*(z+2*(a:ℂ)/(c:ℂ))) =
      lpsQuadraticPhase a c r *
        Complex.exp ((Real.pi:ℂ)*Complex.I*((k:ℂ)+(r.val:ℂ)/(c:ℂ))^2*((c:ℂ)^2*z)) := by sorry
