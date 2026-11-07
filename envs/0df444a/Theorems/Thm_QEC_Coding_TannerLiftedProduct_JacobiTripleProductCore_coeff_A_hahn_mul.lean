-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_A_hahn_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_A_hahn_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:15.876739+00:00
-- url     : https://prove2.me/theorems/c82654e1-41f1-4a90-a972-44c9d2fc38e7
-- title:
--   Jacobi Triple Product Core: coeff A hahn mul
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff A hahn mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1553-L1558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1553-L1558

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_A_hahn_mul (j : ℕ) (F_arg : S_hahn) (b : ℤ) :
    (A_hahn j * F_arg).coeff b = F_arg.coeff (b + 2 * ↑j) := by sorry
