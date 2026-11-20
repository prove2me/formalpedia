-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedFricke_overSpecZ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedFricke_overSpecZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:50:31.049071+00:00
-- url     : https://prove2.me/theorems/0e59737a-f962-4023-83eb-b07dce5a7c87
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Fricke over Spec Z
-- statement:
--   The constructed global Fricke map is an actual morphism over the integer base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L1106-L1114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean#L1106-L1114

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedFricke_overSpecZ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedFricke N hN ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ N hN := by sorry
