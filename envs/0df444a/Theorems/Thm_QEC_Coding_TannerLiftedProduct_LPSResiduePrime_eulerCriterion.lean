-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_eulerCriterion
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.eulerCriterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:43.674131+00:00
-- url     : https://prove2.me/theorems/a66aef92-6d22-4077-984e-9157289d5792
-- title:
--   LPSResidue Prime: euler Criterion
-- statement:
--   The exact Euler-criterion form of the source's residue condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L152-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L152-L155

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

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.eulerCriterion (a : LPSResiduePrime p) :
    (p : ZMod a.q) ^ (a.q / 2) = 1 := by sorry
