-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
-- name    : QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:50.281463+00:00
-- url     : https://prove2.me/theorems/84c00f2c-79cf-4e4c-be61-625ea61e41d9
-- title:
--   Tanner Lifted Product: jacobi Power Series Eval One C T
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Power Series Eval One C T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L58-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L58-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T (m : ℤ) :
    jacobiPowerSeriesEvalOne
        (PowerSeries.C (LaurentPolynomial.T m)) = 1 := by sorry
