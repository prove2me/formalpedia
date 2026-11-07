-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_integerTriangularRoots_iff
-- name    : QEC.Coding.TannerLiftedProduct.mem_integerTriangularRoots_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:15.956528+00:00
-- url     : https://prove2.me/theorems/8290a728-0111-4ef3-97a2-7fce628e0d9b
-- title:
--   Tanner Lifted Product: mem integer Triangular Roots iff
-- statement:
--   The Tanner Lifted Product construction uses the mem integer Triangular Roots iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L21-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L21-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.mem_integerTriangularRoots_iff (n : ℕ) (z : ℤ) :
    z ∈ integerTriangularRoots n ↔ z ^ 2 + z = n := by sorry
