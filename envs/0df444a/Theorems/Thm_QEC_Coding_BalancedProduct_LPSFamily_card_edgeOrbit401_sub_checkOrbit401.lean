-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_edgeOrbit401_sub_checkOrbit401
-- name    : QEC.Coding.BalancedProduct.LPSFamily.card_edgeOrbit401_sub_checkOrbit401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:31.840189+00:00
-- url     : https://prove2.me/theorems/05fac7f1-2e1b-4d7c-9fe8-a4d0882dfef3
-- title:
--   LPSFamily: card edge Orbit401 sub check Orbit401
-- statement:
--   The quotient Tanner rank-nullity gap is exactly `q^2-1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L164-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L164-L171

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

theorem QEC.Coding.BalancedProduct.LPSFamily.card_edgeOrbit401_sub_checkOrbit401
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (EdgeOrbit401 q hq) -
        Fintype.card (CheckOrbit401 q) = q ^ 2 - 1 := by sorry
