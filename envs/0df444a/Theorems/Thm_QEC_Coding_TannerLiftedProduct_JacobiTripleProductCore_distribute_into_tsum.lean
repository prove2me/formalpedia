-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_distribute_into_tsum
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_into_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:02.053293+00:00
-- url     : https://prove2.me/theorems/e7862ddb-2144-4f28-836b-78f5f2e69946
-- title:
--   Jacobi Triple Product Core: distribute into tsum
-- statement:
--   The Jacobi Triple Product Core construction uses the distribute into tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1116-L1127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1116-L1127

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_into_tsum (k : ℕ) : letI := piTop;
    q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      (∑' ℓ : ℕ, (-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' ℓ : ℕ,
      q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by sorry
