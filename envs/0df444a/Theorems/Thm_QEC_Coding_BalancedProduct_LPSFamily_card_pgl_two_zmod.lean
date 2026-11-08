-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_pgl_two_zmod
-- name    : QEC.Coding.BalancedProduct.LPSFamily.card_pgl_two_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:11.652487+00:00
-- url     : https://prove2.me/theorems/89d1c7db-1fc0-413f-8f23-388130ffd96f
-- title:
--   LPSFamily: card pgl two zmod
-- statement:
--   Exact order of the concrete LPS vertex group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L79-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L79-L120

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

theorem QEC.Coding.BalancedProduct.LPSFamily.card_pgl_two_zmod
    (q : Nat) [Fact q.Prime] (hq40 : 40 < q) :
    Fintype.card (PGL(2, ZMod q)) = q * (q ^ 2 - 1) := by sorry
