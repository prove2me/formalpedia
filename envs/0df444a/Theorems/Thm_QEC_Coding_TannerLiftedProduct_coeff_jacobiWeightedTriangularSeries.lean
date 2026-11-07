-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:04.600636+00:00
-- url     : https://prove2.me/theorems/b16021f5-c84b-4887-990e-f7981064408f
-- title:
--   Tanner Lifted Product: coeff jacobi Weighted Triangular Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Weighted Triangular Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L88-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L88-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries (n : ℕ) :
    PowerSeries.coeff n jacobiWeightedTriangularSeries =
      ∑ z ∈ integerTriangularRoots n, (2 * (z : ℚ) + 1) ^ 2 := by sorry
