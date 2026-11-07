-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_sum_interchange
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.sum_interchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:10.715251+00:00
-- url     : https://prove2.me/theorems/aa6ed72a-756a-44ff-a4c2-d303826e6fa9
-- title:
--   Jacobi Triple Product Core: sum interchange
-- statement:
--   The Jacobi Triple Product Core construction uses the sum interchange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1193-L1206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1193-L1206

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.sum_interchange : letI := piTop;
    (∑' k : ℕ, ∑' ℓ : ℕ,
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1 := by sorry
