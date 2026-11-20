-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSecondLevelFunctionField_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:53:46.376633+00:00
-- url     : https://prove2.me/theorems/bdf6c6ac-8df7-425b-9143-17435ece3af4
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Second Level Function Field finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Second Level Function Field finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L280-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L280-L305

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionField_finrank
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    letI := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField =
        (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank (lpsOriginalGeneratedFunctionFieldQ M hM) := by sorry
