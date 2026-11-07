-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_partial_prods_coeff_stable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.partial_prods_coeff_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:01.679289+00:00
-- url     : https://prove2.me/theorems/3cf8f6ae-7479-4338-9ee0-b6cf3fa61b21
-- title:
--   Jacobi Triple Product Core: partial prods coeff stable
-- statement:
--   The Jacobi Triple Product Core construction uses the partial prods coeff stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L300-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L300-L305

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.partial_prods_coeff_stable (x : R) (m n n' : ℕ) (hmn : m < n) (hnn' : n ≤ n') :
    (qPoch (-x * q) (q ^ 2) n' : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by sorry
