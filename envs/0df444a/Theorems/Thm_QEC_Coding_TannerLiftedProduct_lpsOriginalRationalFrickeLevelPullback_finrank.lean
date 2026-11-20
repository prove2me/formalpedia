-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalFrickeLevelPullback_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:02.564615+00:00
-- url     : https://prove2.me/theorems/1027ff67-6155-4fe1-b64b-e494e4da5149
-- title:
--   Tanner Lifted Product: lps Original Rational Fricke Level Pullback finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Fricke Level Pullback finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L79-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L79-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalFrickeLevelPullback_finrank
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM) :=
      (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).toAlgebra
    letI : Module (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM) := Algebra.toModule
    Module.finrank (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM) =
      (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank (lpsOriginalGeneratedFunctionFieldQ M hM) := by sorry
