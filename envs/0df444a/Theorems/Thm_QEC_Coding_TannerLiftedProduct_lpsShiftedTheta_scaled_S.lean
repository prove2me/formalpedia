-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsShiftedTheta_scaled_S
-- name    : QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_scaled_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:06.525698+00:00
-- url     : https://prove2.me/theorems/5fafb9a7-125f-417d-a93c-26574ffb8591
-- title:
--   Tanner Lifted Product: lps Shifted Theta scaled S
-- statement:
--   Positive scaling fixes the square-root branch and contributes exactly 1/c.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L125-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L125-L145

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_scaled_S (a z : ℂ) (c : ℕ) [NeZero c] (hz : 0<z.im) :
    lpsShiftedTheta a ((c:ℂ)^2*(-1/z))=
      ((-Complex.I*z)^(1/2:ℂ)/(c:ℂ))*jacobiTheta₂ a (z/(c:ℂ)^2) := by sorry
