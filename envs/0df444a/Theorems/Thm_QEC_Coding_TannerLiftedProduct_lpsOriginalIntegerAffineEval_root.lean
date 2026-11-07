-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineEval_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineEval_root
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:35:45.421873+00:00
-- url     : https://prove2.me/theorems/6cfbdd0b-d4a9-4a21-a4b3-cf202eca976f
-- title:
--   Tanner Lifted Product: lps Original Integer Affine Eval root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Affine Eval root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L186-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L186-L189

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineEval_root (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalIntegerAffineEval N hN
      (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))=
        lpsOriginalJNHolomorphic N hN := by sorry
