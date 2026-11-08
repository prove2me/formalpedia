-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_checkOrbit401
-- name    : QEC.Coding.BalancedProduct.LPSFamily.card_checkOrbit401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:05.870569+00:00
-- url     : https://prove2.me/theorems/41940d5b-683f-46c4-a685-f9710ff1841c
-- title:
--   LPSFamily: card check Orbit401
-- statement:
--   The free cyclic quotient has exactly `200(q^2-1)` Tanner checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L147-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L147-L161

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.LPSFamily.card_checkOrbit401
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) :
    Fintype.card (CheckOrbit401 q) = 200 * (q ^ 2 - 1) := by sorry
