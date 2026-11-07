-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_psl_two_zmod
-- name    : QEC.Coding.TannerLiftedProduct.card_psl_two_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:38.946526+00:00
-- url     : https://prove2.me/theorems/ebc32470-69b0-4489-b597-01c8af3337c8
-- title:
--   Tanner Lifted Product: card psl two zmod
-- statement:
--   Exact order of `PSL(2,q)` for an odd prime `q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L93-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L93-L105

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

theorem QEC.Coding.TannerLiftedProduct.card_psl_two_zmod
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    Fintype.card PSL(2, ZMod q) = q * (q ^ 2 - 1) / 2 := by sorry
