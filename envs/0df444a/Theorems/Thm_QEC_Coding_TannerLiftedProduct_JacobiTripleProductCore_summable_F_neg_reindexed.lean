-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_F_neg_reindexed
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_F_neg_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:13.334752+00:00
-- url     : https://prove2.me/theorems/419bd792-119c-4b7f-9196-67edf43daa3a
-- title:
--   Jacobi Triple Product Core: summable F neg reindexed
-- statement:
--   The Jacobi Triple Product Core construction uses the summable F neg reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1885-L1889
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1885-L1889

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_F_neg_reindexed : letI := piTop;
    Summable (fun p : ℕ × ℕ => F (-(↑p.1 + 1), p.2)) := by sorry
