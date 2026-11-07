-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_ring_rearrangement
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.ring_rearrangement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:19.33336+00:00
-- url     : https://prove2.me/theorems/ba96dd5e-0a0c-42c8-abb8-69dd836cef15
-- title:
--   Jacobi Triple Product Core: ring rearrangement
-- statement:
--   The Jacobi Triple Product Core construction uses the ring rearrangement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L408-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L408-L417

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.ring_rearrangement (Q : R) (n k : ℕ)
    (P_n P_k P_nk1 a b : R)
    (ih1 : a * P_k * (P_nk1 * (1 - Q * Q ^ (n - (k + 1)))) = P_n)
    (ih2 : b * (P_k * (1 - Q * Q ^ k)) * P_nk1 = P_n)
    (h_alg : (1 - Q * Q ^ k) + Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = 1 - Q * Q ^ n) :
    (a + Q ^ (k + 1) * b) *
      (P_k * (1 - Q * Q ^ k)) *
      (P_nk1 * (1 - Q * Q ^ (n - (k + 1)))) =
    P_n * (1 - Q * Q ^ n) := by sorry
