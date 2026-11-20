-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:53:15.888458+00:00
-- url     : https://prove2.me/theorems/be3e6ae7-9307-4b99-9d91-fd8f67cb3a74
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity To Fricke Localized Chart injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity To Fricke Localized Chart injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L580-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L580-L585

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Injective (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN) := by sorry
