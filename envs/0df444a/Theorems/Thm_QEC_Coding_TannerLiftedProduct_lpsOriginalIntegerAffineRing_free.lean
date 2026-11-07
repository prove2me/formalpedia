-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineRing_free
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineRing_free
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:34:50.767402+00:00
-- url     : https://prove2.me/theorems/bb4f9cb2-9bc6-47bc-817f-e968eaf9cc47
-- title:
--   Tanner Lifted Product: lps Original Integer Affine Ring free
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Affine Ring free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L168-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L168-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineRing_free (N : ℕ) [NeZero N] (hN : 0<N) :
    Module.Free (Polynomial ℤ) (lpsOriginalIntegerAffineRing N hN) := by sorry
