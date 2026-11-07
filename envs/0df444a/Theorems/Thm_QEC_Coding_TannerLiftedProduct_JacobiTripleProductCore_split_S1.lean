-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_split_S1
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.split_S1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:28.100556+00:00
-- url     : https://prove2.me/theorems/5825f416-b5b8-43ae-84b7-092e53f9c9f4
-- title:
--   Jacobi Triple Product Core: split S1
-- statement:
--   The Jacobi Triple Product Core construction uses the split S1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L114-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L114-L120

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.split_S1 (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 =
    1 + ∑ k ∈ Finset.range n,
      qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2 := by sorry
