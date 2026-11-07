-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_combine_sums
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:45.810413+00:00
-- url     : https://prove2.me/theorems/b0749ae6-0d14-4843-816e-695b8d36e89f
-- title:
--   Jacobi Triple Product Core: combine sums
-- statement:
--   The Jacobi Triple Product Core construction uses the combine sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L160-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L160-L173

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_sums (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 +
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by sorry
