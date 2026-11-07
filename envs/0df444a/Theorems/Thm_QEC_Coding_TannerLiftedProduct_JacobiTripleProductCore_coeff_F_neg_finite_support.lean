-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_F_neg_finite_support
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_neg_finite_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:10.875774+00:00
-- url     : https://prove2.me/theorems/a4dbedb7-e866-40f6-a417-534ef8f09bf3
-- title:
--   Jacobi Triple Product Core: coeff F neg finite support
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff F neg finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1877-L1883
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1877-L1883

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_neg_finite_support (d : ℕ) :
    ∃ (S_fin : Finset (ℕ × ℕ)), ∀ p : ℕ × ℕ, p ∉ S_fin →
      (PowerSeries.coeff d) (F (-(↑p.1 + 1), p.2)) = 0 := by sorry
