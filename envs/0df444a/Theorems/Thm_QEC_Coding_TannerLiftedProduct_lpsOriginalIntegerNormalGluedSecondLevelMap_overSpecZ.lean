-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:57:37.103163+00:00
-- url     : https://prove2.me/theorems/82f34a16-ab92-4132-9764-857b4e32a814
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Second Level Map over Spec Z
-- statement:
--   The genuine finite second map is over Z, hence defines integral correspondence data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L341-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L341-L350

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hN = lpsOriginalIntegerNormalGluedToSpecZ M hM := by sorry
