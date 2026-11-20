-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:57:41.069731+00:00
-- url     : https://prove2.me/theorems/873d9846-0c15-4caf-9f96-7a0e0917b4c7
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Second Level Function Field Pullback naturality
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Second Level Function Field Pullback naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L246-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L246-L277

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM) =
    (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom := by sorry
