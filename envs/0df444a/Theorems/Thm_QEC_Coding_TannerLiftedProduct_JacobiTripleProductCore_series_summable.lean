-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_series_summable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.series_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:01.869334+00:00
-- url     : https://prove2.me/theorems/4fe4f729-aece-4a53-82d4-eeaf0a8cb6ab
-- title:
--   Jacobi Triple Product Core: series summable
-- statement:
--   The Jacobi Triple Product Core construction uses the series summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L372-L376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L372-L376

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.series_summable (x : R) : letI := piTop;
    Summable fun k : ℕ => q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 := by sorry
