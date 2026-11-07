-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_rhs_finite_support
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_rhs_finite_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:24.519492+00:00
-- url     : https://prove2.me/theorems/4d3f9712-2632-486a-aa69-aa8003dec41f
-- title:
--   Jacobi Triple Product Core: coeff rhs finite support
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff rhs finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1277-L1284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1277-L1284

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_rhs_finite_support (d : ℕ) :
    (Function.support (fun m : ℤ =>
      (PowerSeries.coeff d) (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2))).Finite := by sorry
