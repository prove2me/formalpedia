-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_finiteOverOrder
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalAffine_finiteOverOrder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:36:50.182194+00:00
-- url     : https://prove2.me/theorems/d2f2a3f6-3179-43b0-b408-b9878d25dbb0
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Affine finite Over Order
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Affine finite Over Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L670-L687
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L670-L687

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalAffine_finiteOverOrder
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerAffineToNormal N hN).toRingHom.toAlgebra
    Module.Finite (lpsOriginalIntegerAffineRing N hN)
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by sorry
