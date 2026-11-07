-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_of_trunc_one
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_mul_of_trunc_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:19.019917+00:00
-- url     : https://prove2.me/theorems/70ae172b-bd0d-46f9-b158-66a1fd558a1f
-- title:
--   Jacobi Triple Product Core: coeff mul of trunc one
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff mul of trunc one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L276-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L276-L280

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_mul_of_trunc_one (f g : R) (m : ℕ)
    (hg : ∀ j ≤ m, g.coeff j = if j = 0 then 1 else 0) :
    (f * g).coeff m = f.coeff m := by sorry
