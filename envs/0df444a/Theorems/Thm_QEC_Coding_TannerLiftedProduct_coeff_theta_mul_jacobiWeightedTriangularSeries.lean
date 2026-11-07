-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_theta_mul_jacobiWeightedTriangularSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_theta_mul_jacobiWeightedTriangularSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:16:06.085266+00:00
-- url     : https://prove2.me/theorems/5c3773ce-538a-46dc-bd12-fc1036f6c1d5
-- title:
--   Tanner Lifted Product: coeff theta mul jacobi Weighted Triangular Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff theta mul jacobi Weighted Triangular Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L395-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L395-L423

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_theta_mul_jacobiWeightedTriangularSeries (n : ℕ) :
    PowerSeries.coeff n
        (rationalIntegerThetaSeries * jacobiWeightedTriangularSeries) =
      ∑ p : JacobiReindexedPair n, (2 * (p.1.1 : ℚ) + 1) ^ 2 := by sorry
