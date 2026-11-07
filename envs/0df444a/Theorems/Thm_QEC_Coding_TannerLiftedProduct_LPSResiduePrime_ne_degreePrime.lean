-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_ne_degreePrime
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.ne_degreePrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:31:02.571769+00:00
-- url     : https://prove2.me/theorems/df161dcd-f4e7-43dc-8017-011730a6a9ad
-- title:
--   LPSResidue Prime: ne degree Prime
-- statement:
--   The LPSResidue Prime construction uses the ne degree Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L120-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L120-L124

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.ne_degreePrime (a : LPSResiduePrime p) :
    a.q ≠ p := by sorry
