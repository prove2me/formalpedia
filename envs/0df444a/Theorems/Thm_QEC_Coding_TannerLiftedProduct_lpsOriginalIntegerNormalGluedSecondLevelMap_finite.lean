-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedSecondLevelMap_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedSecondLevelMap_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:54:10.001246+00:00
-- url     : https://prove2.me/theorems/2dd1bf9e-611d-4d2d-abc9-5fc35becf7b3
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Second Level Map finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Second Level Map finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L137-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L137-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedSecondLevelMap_finite
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM) := by sorry
