-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_support_finset_Z_nat
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.support_finset_Z_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:59.660999+00:00
-- url     : https://prove2.me/theorems/d24af0c8-9671-42dc-941d-3e581a328d96
-- title:
--   Jacobi Triple Product Core: support finset Z nat
-- statement:
--   The Jacobi Triple Product Core construction uses the support finset Z nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1833-L1848
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1833-L1848

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
set_option maxHeartbeats 800000

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.support_finset_Z_nat (d : ℕ) :
    ∃ (S_fin : Finset (ℤ × ℕ)), ∀ (z : ℤ) (ℓ : ℕ),
      (z + ↑ℓ).natAbs ^ 2 + ℓ ≤ d → (z, ℓ) ∈ S_fin := by sorry
