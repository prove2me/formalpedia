-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_summand_vanishes
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_summand_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:11.201734+00:00
-- url     : https://prove2.me/theorems/359e4f3f-52b8-4335-b322-86198e0ff7f5
-- title:
--   Jacobi Triple Product Core: coeff summand vanishes
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff summand vanishes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1167-L1173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1167-L1173

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_summand_vanishes (k ℓ d : ℕ) (h : d < (k + ℓ) ^ 2 + ℓ) :
    (PowerSeries.coeff d)
      (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
       ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by sorry
