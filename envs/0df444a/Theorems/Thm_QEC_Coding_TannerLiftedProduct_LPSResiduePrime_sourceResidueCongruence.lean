-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_sourceResidueCongruence
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.sourceResidueCongruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:38.785194+00:00
-- url     : https://prove2.me/theorems/ead623b5-5198-4551-b6fb-b856a902c9e2
-- title:
--   LPSResidue Prime: source Residue Congruence
-- statement:
--   The residue hypothesis in the exact natural-number congruence form printed
--   in PK22 Example 2.4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L159-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L159-L173

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

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.sourceResidueCongruence (a : LPSResiduePrime p) :
    p ^ ((a.q - 1) / 2) % a.q = 1 := by sorry
