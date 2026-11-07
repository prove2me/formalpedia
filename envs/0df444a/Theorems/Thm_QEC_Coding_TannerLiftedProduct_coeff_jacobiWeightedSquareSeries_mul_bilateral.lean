-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries_mul_bilateral
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries_mul_bilateral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:16:27.449521+00:00
-- url     : https://prove2.me/theorems/ce550d93-21f9-4948-a4be-f98eca3d3a2d
-- title:
--   Tanner Lifted Product: coeff jacobi Weighted Square Series mul bilateral
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Weighted Square Series mul bilateral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L425-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L425-L458

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries_mul_bilateral (n : ℕ) :
    PowerSeries.coeff n
        (jacobiWeightedSquareSeries * rationalBilateralTriangularSeries) =
      ∑ p : JacobiReindexedPair n, (2 * (p.1.2 : ℚ)) ^ 2 := by sorry
