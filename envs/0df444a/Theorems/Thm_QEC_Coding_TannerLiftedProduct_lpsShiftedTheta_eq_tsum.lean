-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsShiftedTheta_eq_tsum
-- name    : QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_eq_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:10.935062+00:00
-- url     : https://prove2.me/theorems/7afec94c-1f25-4fc1-a6b8-1003a2e1b2de
-- title:
--   Tanner Lifted Product: lps Shifted Theta eq tsum
-- statement:
--   Complete the square in the actual Jacobi series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L28-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L28-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_eq_tsum (a z : ℂ) : lpsShiftedTheta a z =
    ∑' n : ℤ, Complex.exp ((Real.pi:ℂ)*Complex.I*((n:ℂ)+a)^2*z) := by sorry
