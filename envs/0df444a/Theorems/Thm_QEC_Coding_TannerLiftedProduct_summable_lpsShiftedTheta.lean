-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_lpsShiftedTheta
-- name    : QEC.Coding.TannerLiftedProduct.summable_lpsShiftedTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:49.07281+00:00
-- url     : https://prove2.me/theorems/71d735e3-7a7c-4459-8c8d-6a5ed34d3846
-- title:
--   Tanner Lifted Product: summable lps Shifted Theta
-- statement:
--   Absolute summability is inherited from Jacobi theta on the upper half plane.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L39-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L39-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.summable_lpsShiftedTheta (a z : ℂ) (hz : 0<z.im) :
    Summable (fun n : ℤ => Complex.exp ((Real.pi:ℂ)*Complex.I*((n:ℂ)+a)^2*z)) := by sorry
