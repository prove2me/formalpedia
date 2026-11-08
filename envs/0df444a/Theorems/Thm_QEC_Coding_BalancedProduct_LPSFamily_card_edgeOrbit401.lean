-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_edgeOrbit401
-- name    : QEC.Coding.BalancedProduct.LPSFamily.card_edgeOrbit401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:20.695204+00:00
-- url     : https://prove2.me/theorems/3791fd11-a859-4e71-9e7b-c3a9c9d61601
-- title:
--   LPSFamily: card edge Orbit401
-- statement:
--   The free cyclic quotient has exactly `201(q^2-1)` Tanner bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L129-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L129-L144

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

theorem QEC.Coding.BalancedProduct.LPSFamily.card_edgeOrbit401
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (EdgeOrbit401 q hq) = 201 * (q ^ 2 - 1) := by sorry
