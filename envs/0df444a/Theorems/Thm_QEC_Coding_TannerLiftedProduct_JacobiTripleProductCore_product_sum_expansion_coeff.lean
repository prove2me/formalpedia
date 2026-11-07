-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_product_sum_expansion_coeff
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_sum_expansion_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:21.563199+00:00
-- url     : https://prove2.me/theorems/fd1d005b-9779-48b0-b721-7900200480cd
-- title:
--   Jacobi Triple Product Core: product sum expansion coeff
-- statement:
--   The Jacobi Triple Product Core construction uses the product sum expansion coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1038-L1044
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1038-L1044

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_sum_expansion_coeff (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) : R).coeff m := by sorry
