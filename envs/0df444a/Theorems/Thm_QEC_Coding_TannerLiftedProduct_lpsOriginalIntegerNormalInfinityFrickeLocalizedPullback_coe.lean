-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:53:29.503269+00:00
-- url     : https://prove2.me/theorems/88fe7b8f-5c32-40f3-b791-e36b13c95944
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity Fricke Localized Pullback coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity Fricke Localized Pullback coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L693-L698
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L693-L698

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback_coe
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback N hN x).val =
      lpsOriginalRationalFrickePullback N hN x.val := by sorry
