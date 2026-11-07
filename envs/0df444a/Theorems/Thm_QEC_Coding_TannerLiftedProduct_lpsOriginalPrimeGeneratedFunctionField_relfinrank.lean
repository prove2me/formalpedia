-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGeneratedFunctionField_relfinrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGeneratedFunctionField_relfinrank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:10:28.584418+00:00
-- url     : https://prove2.me/theorems/a6e1df4d-5a28-4067-815c-2ac271da46d6
-- title:
--   Tanner Lifted Product: lps Original Prime Generated Function Field relfinrank
-- statement:
--   The same original coprime-prime function-field extension has degree p+1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeFunctionFieldDegree.lean#L79-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeFunctionFieldDegree.lean#L79-L89

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGeneratedFunctionField_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (hposN : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField (N*p)
        (Nat.mul_pos hposN (Fact.out : p.Prime).pos)) = p+1 := by sorry
