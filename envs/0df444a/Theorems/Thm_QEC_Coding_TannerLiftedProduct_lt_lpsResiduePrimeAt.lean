-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_lpsResiduePrimeAt
-- name    : QEC.Coding.TannerLiftedProduct.lt_lpsResiduePrimeAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:50.083524+00:00
-- url     : https://prove2.me/theorems/41706da1-e5ae-4670-98ec-cad5104a25b6
-- title:
--   Tanner Lifted Product: lt lps Residue Prime At
-- statement:
--   The computed source-compatible quotient prime is above the requested bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L298-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L298-L301

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

theorem QEC.Coding.TannerLiftedProduct.lt_lpsResiduePrimeAt
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    B < (lpsResiduePrimeAt hp hp4 B).q := by sorry
