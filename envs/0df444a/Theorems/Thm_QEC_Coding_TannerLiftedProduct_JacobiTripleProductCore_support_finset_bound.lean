-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_support_finset_bound
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.support_finset_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:13.228757+00:00
-- url     : https://prove2.me/theorems/ae02e061-6a6c-4ddb-b9d1-abdf22a4f0be
-- title:
--   Jacobi Triple Product Core: support finset bound
-- statement:
--   The Jacobi Triple Product Core construction uses the support finset bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1141-L1146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1141-L1146

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.support_finset_bound (d : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)), ∀ (k ℓ : ℕ),
      ((k + ℓ) ^ 2 + ℓ : ℕ) ≤ d → (k, ℓ) ∈ S := by sorry
