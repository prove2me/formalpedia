-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:25.841171+00:00
-- url     : https://prove2.me/theorems/ae31e3a0-728f-442e-892b-e9cad11e3c53
-- title:
--   Tanner Lifted Product: coeff jacobi Signed Cube Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Signed Cube Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L344-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L344-L349

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries (n : ℕ) :
    PowerSeries.coeff n jacobiSignedCubeSeries =
      (1 / 2 : ℚ) *
        ∑ z : {z : ℤ // z ∈ integerTriangularRoots (2 * n)},
          jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1) := by sorry
