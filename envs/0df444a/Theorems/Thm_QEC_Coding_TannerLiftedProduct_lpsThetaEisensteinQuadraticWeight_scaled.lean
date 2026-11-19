-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinQuadraticWeight_scaled
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinQuadraticWeight_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:11.494188+00:00
-- url     : https://prove2.me/theorems/b45fe848-7ef2-4c32-9609-8f1ab88a40ae
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Quadratic Weight scaled
-- statement:
--   The genuine quadratic weights and character multipliers reproduce the negative two-power weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L83-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L83-L99

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinQuadraticWeight_scaled (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) :
    lpsThetaEisensteinQuadraticWeight q a*lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)/
      ((2^a.val:ℕ):ℂ)^2= -lpsThetaEisensteinTwoWeight a/((2^a.val:ℕ):ℂ) := by sorry
