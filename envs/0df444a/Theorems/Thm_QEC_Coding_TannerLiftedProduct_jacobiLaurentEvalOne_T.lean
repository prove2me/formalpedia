-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
-- name    : QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:07.389948+00:00
-- url     : https://prove2.me/theorems/e136b0ae-accc-43d2-9f69-a32a2baef656
-- title:
--   Tanner Lifted Product: jacobi Laurent Eval One T
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Laurent Eval One T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L30-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T (m : ℤ) :
    jacobiLaurentEvalOne (LaurentPolynomial.T m) = 1 := by sorry
