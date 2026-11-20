-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroFrickePullback_involutive
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroFrickePullback_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:52:05.290249+00:00
-- url     : https://prove2.me/theorems/bd949681-f04f-40fe-9c9e-5ed560fb447e
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero Fricke Pullback involutive
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero Fricke Pullback involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L179-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L179-L186

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroFrickePullback_involutive
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Involutive (lpsOriginalIntegerNormalZeroFrickePullback N hN) := by sorry
