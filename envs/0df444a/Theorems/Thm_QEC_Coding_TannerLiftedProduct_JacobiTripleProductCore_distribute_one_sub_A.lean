-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_distribute_one_sub_A
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_one_sub_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:26.437831+00:00
-- url     : https://prove2.me/theorems/ba430ac4-3b0f-4ff1-b394-a28902002113
-- title:
--   Jacobi Triple Product Core: distribute one sub A
-- statement:
--   The Jacobi Triple Product Core construction uses the distribute one sub A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L99-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L99-L112

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_one_sub_A (A Q : R) (n : ℕ) :
    (1 - A) * ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 =
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 +
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by sorry
