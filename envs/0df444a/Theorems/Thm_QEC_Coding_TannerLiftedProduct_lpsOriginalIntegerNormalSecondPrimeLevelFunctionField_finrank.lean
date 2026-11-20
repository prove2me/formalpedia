-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSecondPrimeLevelFunctionField_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondPrimeLevelFunctionField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:32.679174+00:00
-- url     : https://prove2.me/theorems/5a66251d-d032-4415-8a12-415d57f6aec6
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Second Prime Level Function Field finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Second Prime Level Function Field finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L307-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L307-L326

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondPrimeLevelFunctionField_finrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)
    letI := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).functionField = p+1 := by sorry
