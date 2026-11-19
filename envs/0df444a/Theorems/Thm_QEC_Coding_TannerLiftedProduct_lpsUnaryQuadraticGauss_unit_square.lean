-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_unit_square
-- name    : QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_unit_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:22.341386+00:00
-- url     : https://prove2.me/theorems/69448254-5804-416b-a4bb-a743c6940514
-- title:
--   Tanner Lifted Product: lps Unary Quadratic Gauss unit square
-- statement:
--   Multiplication by an actual unit reindexes the quadratic Gauss sum by its square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L18-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L18-L29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_unit_square (N : ℕ) [NeZero N] (a d : ℤ)
    (hd : IsUnit (d:ZMod N)) :
    lpsUnaryQuadraticGauss (a*d^2) N=lpsUnaryQuadraticGauss a N := by sorry
