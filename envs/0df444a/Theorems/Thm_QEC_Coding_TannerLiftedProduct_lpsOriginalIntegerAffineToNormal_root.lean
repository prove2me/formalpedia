-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineToNormal_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineToNormal_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:35:57.603204+00:00
-- url     : https://prove2.me/theorems/7256a0ca-8f37-46e6-9b82-ebfd83df48c4
-- title:
--   Tanner Lifted Product: lps Original Integer Affine To Normal root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Affine To Normal root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L606-L618
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L606-L618

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineToNormal_root
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    ((lpsOriginalIntegerAffineToNormal N hN
      (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))).val.val)=
        lpsOriginalJNInFractionField N hN := by sorry
