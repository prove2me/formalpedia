-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_reassemble_sum
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.reassemble_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:33.70464+00:00
-- url     : https://prove2.me/theorems/973c6c52-c52f-4b8f-8618-df33f1aa1114
-- title:
--   Jacobi Triple Product Core: reassemble sum
-- statement:
--   The Jacobi Triple Product Core construction uses the reassemble sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L148-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L148-L158

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.reassemble_sum (A Q : R) (n : ℕ) :
    1 + ∑ k ∈ Finset.range n,
      qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 +
    (-A) ^ (n + 1) * Q ^ (n + 1).choose 2 =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by sorry
