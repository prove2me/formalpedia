-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
-- name    : QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:12.100087+00:00
-- url     : https://prove2.me/theorems/ba2a566a-8496-4772-a486-2829133500af
-- title:
--   Tanner Lifted Product: integer Triangular Roots zero
-- statement:
--   The Tanner Lifted Product construction uses the integer Triangular Roots zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L35-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L35-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero :
    integerTriangularRoots 0 = {-1, 0} := by sorry
