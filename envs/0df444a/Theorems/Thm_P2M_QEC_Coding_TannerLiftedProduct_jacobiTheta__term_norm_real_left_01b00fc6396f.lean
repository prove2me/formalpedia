-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_jacobiTheta__term_norm_real_left_01b00fc6396f
-- name    : P2M_QEC_Coding_TannerLiftedProduct_jacobiTheta__term_norm_real_left_01b00fc6396f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:11.475733+00:00
-- url     : https://prove2.me/theorems/11e95fbf-42c1-41d0-85aa-b1423ad776aa
-- title:
--   P2 M QEC Coding Tanner Lifted Product jacobi Theta  term norm real left 01b00fc6396f: P2 M QEC Coding Tanner Lifted Product jacobi Theta  term norm real left 01b00fc6396f
-- statement:
--   Real characteristic phases have norm one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L164-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L164-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem P2M_QEC_Coding_TannerLiftedProduct_jacobiTheta__term_norm_real_left_01b00fc6396f (n : ℤ) (a : ℝ) (z : ℂ) :
    ‖jacobiTheta₂_term n (a:ℂ) z‖=‖Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z)‖ := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«jacobiTheta₂_term_norm_real_left» := P2M_QEC_Coding_TannerLiftedProduct_jacobiTheta__term_norm_real_left_01b00fc6396f
