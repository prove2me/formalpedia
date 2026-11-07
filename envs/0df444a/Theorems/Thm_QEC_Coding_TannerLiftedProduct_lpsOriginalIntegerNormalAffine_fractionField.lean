-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_fractionField
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalAffine_fractionField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:16:35.867193+00:00
-- url     : https://prove2.me/theorems/11ac4567-f371-48be-9175-c86b79285885
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Affine fraction Field
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Affine fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L476-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L476-L494

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalAffine_fractionField
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsFractionRing
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by sorry
