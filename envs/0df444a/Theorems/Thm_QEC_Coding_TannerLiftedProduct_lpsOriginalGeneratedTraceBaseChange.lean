-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedTraceBaseChange
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedTraceBaseChange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:35:23.997903+00:00
-- url     : https://prove2.me/theorems/2e644869-694a-4fe5-a2d1-4aa84ea9ea06
-- title:
--   Tanner Lifted Product: lps Original Generated Trace Base Change
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Generated Trace Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L125-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L125-L142

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary001
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary004

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedTraceBaseChange
    (N : ℕ) [NeZero N] (hN : 0 < N) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    Algebra.trace (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)
      (lpsOriginalGeneratedQToComplex N hN x) =
    lpsOriginalJBaseQToC
      (Algebra.trace (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) x) := by sorry
