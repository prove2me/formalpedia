-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_vertex401
-- name    : QEC.Coding.BalancedProduct.LPSFamily.card_vertex401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:39.998554+00:00
-- url     : https://prove2.me/theorems/f5bd4836-51fe-4783-a8a1-f0edaeb12e2a
-- title:
--   LPSFamily: card vertex401
-- statement:
--   Exact LPS vertex count in the notation of the Tanner construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L123-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L123-L126

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

theorem QEC.Coding.BalancedProduct.LPSFamily.card_vertex401
    (q : Nat) [Fact q.Prime] (hq40 : 40 < q) :
    Fintype.card (Vertex401 q) = q * (q ^ 2 - 1) := by sorry
