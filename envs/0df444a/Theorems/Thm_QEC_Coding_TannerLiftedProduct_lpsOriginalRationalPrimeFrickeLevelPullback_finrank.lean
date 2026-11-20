-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalPrimeFrickeLevelPullback_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPrimeFrickeLevelPullback_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:53:46.10351+00:00
-- url     : https://prove2.me/theorems/0b9349ad-1c89-4930-b074-25c4dfad3e00
-- title:
--   Tanner Lifted Product: lps Original Rational Prime Fricke Level Pullback finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Prime Fricke Level Pullback finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L111-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L111-L126

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPrimeFrickeLevelPullback_finrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    letI : Module (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := Algebra.toModule
    Module.finrank (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) = p+1 := by sorry
