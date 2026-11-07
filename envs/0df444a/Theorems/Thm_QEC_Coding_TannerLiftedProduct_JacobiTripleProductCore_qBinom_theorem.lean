-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_theorem
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:41.288191+00:00
-- url     : https://prove2.me/theorems/770328cd-96b3-4561-9bd4-7188d97673a1
-- title:
--   Jacobi Triple Product Core: q Binom theorem
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L189-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L189-L194

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_theorem (A Q : R) (n : ℕ) :
    qPoch A Q n =
    ∑ k ∈ Finset.range (n + 1), qBinom Q n k * (-A) ^ k * Q ^ k.choose 2 := by sorry
