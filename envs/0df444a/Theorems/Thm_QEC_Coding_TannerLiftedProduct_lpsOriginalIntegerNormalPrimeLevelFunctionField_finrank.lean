-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalPrimeLevelFunctionField_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalPrimeLevelFunctionField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:16:03.311711+00:00
-- url     : https://prove2.me/theorems/1624fdee-6a98-41e3-9106-c5e95690df7f
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Prime Level Function Field finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Prime Level Function Field finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L361-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L361-L380

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalPrimeLevelFunctionField_finrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)
    letI := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)).functionField = p+1 := by sorry
