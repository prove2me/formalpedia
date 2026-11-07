-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_single_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_single_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:50.167295+00:00
-- url     : https://prove2.me/theorems/efa92319-b48f-4805-8de4-77ffff971bd1
-- title:
--   Jacobi Triple Product Core: coeff single mul
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1775-L1779
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1775-L1779

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_single_mul (j d : ℕ) (tail : S_hahn) :
    (HahnSeries.single ((j + 1 : ℤ) ^ 2) (1 : LaurentPolynomial ℤ) * tail).coeff (↑d) =
    tail.coeff ((d : ℤ) - (j + 1 : ℤ) ^ 2) := by sorry
