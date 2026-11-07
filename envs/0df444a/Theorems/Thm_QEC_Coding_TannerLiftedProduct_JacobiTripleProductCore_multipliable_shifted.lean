-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_shifted
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.multipliable_shifted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:34.298207+00:00
-- url     : https://prove2.me/theorems/f84c58a7-7a94-4f4b-bea9-037602a0e579
-- title:
--   Jacobi Triple Product Core: multipliable shifted
-- statement:
--   The Jacobi Triple Product Core construction uses the multipliable shifted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L908-L917
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L908-L917

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.multipliable_shifted (k : ℕ) : letI := piTop;
    Multipliable (fun n ↦ 1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n) := by sorry
