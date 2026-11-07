-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineGenerated_isFractionRing
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineGenerated_isFractionRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:22:25.599374+00:00
-- url     : https://prove2.me/theorems/e371ecf0-0e8a-4da5-aee8-3379722c7e5d
-- title:
--   Tanner Lifted Product: lps Original Integer Affine Generated is Fraction Ring
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Affine Generated is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L621-L650
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L621-L650

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineGenerated_isFractionRing
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerAffineToGenerated N hN).toAlgebra
    IsFractionRing (lpsOriginalIntegerAffineRing N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by sorry
