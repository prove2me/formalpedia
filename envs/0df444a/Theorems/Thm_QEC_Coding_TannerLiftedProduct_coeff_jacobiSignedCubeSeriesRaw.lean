-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:45.150007+00:00
-- url     : https://prove2.me/theorems/cd256df0-6a3f-4b47-be5a-277baa537ce1
-- title:
--   Tanner Lifted Product: coeff jacobi Signed Cube Series Raw
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Signed Cube Series Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L333-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L333-L337

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw (n : ℕ) :
    PowerSeries.coeff n jacobiSignedCubeSeriesRaw =
      ∑ z : {z : ℤ // z ∈ integerTriangularRoots (2 * n)},
        jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1) := by sorry
