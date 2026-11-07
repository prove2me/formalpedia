-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_card_psl
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.card_psl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:48.707573+00:00
-- url     : https://prove2.me/theorems/ebe0ca39-f102-40d5-94e9-33436f69aee7
-- title:
--   LPSResidue Prime: card psl
-- statement:
--   Exact order of the source's LPS vertex group at this arithmetic index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L176-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L176-L180

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

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.card_psl (a : LPSResiduePrime p) :
    Fintype.card PSL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) / 2 := by sorry
