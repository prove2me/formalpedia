-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParitySign_add
-- name    : QEC.Coding.TannerLiftedProduct.jacobiParitySign_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:42.587886+00:00
-- url     : https://prove2.me/theorems/7e0da7af-0609-499e-aeab-44d59caed305
-- title:
--   Tanner Lifted Product: jacobi Parity Sign add
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Parity Sign add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L123-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L123-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.jacobiParitySign_add (k l : ℤ) :
    jacobiParitySign k * jacobiParitySign l =
      jacobiParitySign (k + l) := by sorry
