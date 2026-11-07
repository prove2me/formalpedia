-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_split_S2
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.split_S2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:29.798626+00:00
-- url     : https://prove2.me/theorems/17c85780-c798-475e-8bbc-befe1dbf73fa
-- title:
--   Jacobi Triple Product Core: split S2
-- statement:
--   The Jacobi Triple Product Core construction uses the split S2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L122-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L122-L129

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.split_S2 (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    (∑ k ∈ Finset.range n,
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2) +
    (-A) ^ (n + 1) * Q ^ (n + 1).choose 2 := by sorry
