-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_mul_series
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_mul_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:19.740169+00:00
-- url     : https://prove2.me/theorems/73fddf29-a929-4572-8352-9a56b9deb215
-- title:
--   Jacobi Triple Product Core: summable mul series
-- statement:
--   The Jacobi Triple Product Core construction uses the summable mul series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L971-L977
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L971-L977

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_mul_series (x : R) : letI := piTop;
    Summable fun k : ℕ => qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) := by sorry
