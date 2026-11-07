-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
-- name    : QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:45.363906+00:00
-- url     : https://prove2.me/theorems/b9d8329b-727c-465b-b3d3-decdb3974374
-- title:
--   Tanner Lifted Product: lps Residue Prime At q
-- statement:
--   The Tanner Lifted Product construction uses the lps Residue Prime At q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L293-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L293-L295

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

theorem QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsResiduePrimeAt hp hp4 B).q = lpsLeastPrimeAbove hp B := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
