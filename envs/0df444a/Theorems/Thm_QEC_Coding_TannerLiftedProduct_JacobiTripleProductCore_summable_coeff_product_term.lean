-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_coeff_product_term
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_coeff_product_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:38.350661+00:00
-- url     : https://prove2.me/theorems/ffd0e49c-eb51-48cc-b62c-8e32ae673bab
-- title:
--   Jacobi Triple Product Core: summable coeff product term
-- statement:
--   The Jacobi Triple Product Core construction uses the summable coeff product term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L785-L800
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L785-L800

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_coeff_product_term {x : R} (hx : x.constantCoeff = 0)
    (p q : S) (d : ℕ) :
    Summable (fun (kl : ℕ × ℕ) =>
      (PowerSeries.coeff d)
        ((p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2))) := by sorry
