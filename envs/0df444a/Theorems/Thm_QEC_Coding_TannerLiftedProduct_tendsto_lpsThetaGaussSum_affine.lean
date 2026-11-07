-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_lpsThetaGaussSum_affine
-- name    : QEC.Coding.TannerLiftedProduct.tendsto_lpsThetaGaussSum_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:43:41.386697+00:00
-- url     : https://prove2.me/theorems/5e4d116b-3d48-4dea-ad4c-c8a40a6cb763
-- title:
--   Tanner Lifted Product: tendsto lps Theta Gauss Sum affine
-- statement:
--   The actual finite characteristic transform converges to its Gauss sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L244-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L244-L250

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.tendsto_lpsThetaGaussSum_affine (a : ℤ) (c : ℕ) (t d : ℝ) (ht : 0<t) :
    Tendsto (fun z : UpperHalfPlane => lpsThetaGaussSum a c (((z:ℂ)+(d:ℂ))/(t:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (lpsUnaryQuadraticGauss a c)) := by sorry
