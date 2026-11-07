-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_product_term
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_product_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:39.996118+00:00
-- url     : https://prove2.me/theorems/c653d6d8-2ac2-41f3-b17c-b1507e4f3f16
-- title:
--   Jacobi Triple Product Core: summable product term
-- statement:
--   The Jacobi Triple Product Core construction uses the summable product term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L802-L808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L802-L808

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_product_term {x : R} (hx : x.constantCoeff = 0) (p q : S) :
    letI := piTop;
    Summable (fun (kl : ℕ × ℕ) => (p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2)) := by sorry
