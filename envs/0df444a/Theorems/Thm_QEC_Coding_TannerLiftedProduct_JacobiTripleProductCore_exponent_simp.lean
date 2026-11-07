-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_simp
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_simp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:53.27429+00:00
-- url     : https://prove2.me/theorems/9d2934c3-052f-4edb-9e53-c9dcd178646f
-- title:
--   Jacobi Triple Product Core: exponent simp
-- statement:
--   The Jacobi Triple Product Core construction uses the exponent simp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L325-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L325-L338

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_simp (x : R) (k : ℕ) :
    (-(-x * q)) ^ k * (q ^ 2) ^ k.choose 2 = q ^ (k ^ 2) * x ^ k := by sorry
