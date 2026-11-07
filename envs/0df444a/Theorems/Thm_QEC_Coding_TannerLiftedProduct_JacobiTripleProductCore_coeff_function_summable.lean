-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_function_summable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_function_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:18.597898+00:00
-- url     : https://prove2.me/theorems/2463f02b-c5ad-4cfb-bb9f-16deffcdbfbe
-- title:
--   Jacobi Triple Product Core: coeff function summable
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff function summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1175-L1183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1175-L1183

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_function_summable (d : ℕ) :
    Summable (fun (p : ℕ × ℕ) =>
      (PowerSeries.coeff d)
        (PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
         ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
         PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1)) := by sorry
