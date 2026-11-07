-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:11.962435+00:00
-- url     : https://prove2.me/theorems/f63d7720-c7ec-4ad4-a458-7c213c86bf2e
-- title:
--   Jacobi Triple Product Core: summand eq
-- statement:
--   The Jacobi Triple Product Core construction uses the summand eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L666-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L666-L685

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_eq {n k : ℕ} (hkn : k ≤ n) :
    aCoeff (n - k) * bCoeff k =
    (-1) ^ n * PowerSeries.invOfUnit (P n) 1 *
      (qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2) := by sorry
