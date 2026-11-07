-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_product_term_coeff_vanishes
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_term_coeff_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:09.261192+00:00
-- url     : https://prove2.me/theorems/5c548fbc-7571-4de9-8d6f-177f9d85e63e
-- title:
--   Jacobi Triple Product Core: product term coeff vanishes
-- statement:
--   The Jacobi Triple Product Core construction uses the product term coeff vanishes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L961-L969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L961-L969

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_term_coeff_vanishes (x : R) (m k : ℕ) (hk : m < k) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m = 0 := by sorry
