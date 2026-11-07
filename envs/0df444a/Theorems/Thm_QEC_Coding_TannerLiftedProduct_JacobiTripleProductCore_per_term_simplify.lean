-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_per_term_simplify
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.per_term_simplify
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:03.315206+00:00
-- url     : https://prove2.me/theorems/db4b8a0a-7526-4083-98c7-bde358d35900
-- title:
--   Jacobi Triple Product Core: per term simplify
-- statement:
--   The Jacobi Triple Product Core construction uses the per term simplify property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L947-L959
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L947-L959

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.per_term_simplify (x : R) (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) =
    q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) := by sorry
