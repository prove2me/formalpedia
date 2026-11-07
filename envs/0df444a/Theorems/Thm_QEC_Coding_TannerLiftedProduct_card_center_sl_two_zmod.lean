-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_center_sl_two_zmod
-- name    : QEC.Coding.TannerLiftedProduct.card_center_sl_two_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:30.254205+00:00
-- url     : https://prove2.me/theorems/7e1e85f8-6aea-4ab2-95f1-12d91e7fa8e9
-- title:
--   Tanner Lifted Product: card center sl two zmod
-- statement:
--   For odd prime `q`, the center of `SL(2,q)` consists of the two scalar
--   matrices `±I`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L82-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L82-L90

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

theorem QEC.Coding.TannerLiftedProduct.card_center_sl_two_zmod
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    Nat.card (Subgroup.center SL(2, ZMod q)) = 2 := by sorry
