-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_neg_div
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_neg_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:39.471196+00:00
-- url     : https://prove2.me/theorems/7770bcb9-10ad-47fb-afff-cea1a7db2440
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Character neg div
-- statement:
--   Quadratic inversion and the proved value at minus one remove the cusp quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L71-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L71-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_neg_div (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (A D : ZMod q) : lpsQuadraticE2Character q (-A/D)=lpsQuadraticE2Character q (A*D) := by sorry
