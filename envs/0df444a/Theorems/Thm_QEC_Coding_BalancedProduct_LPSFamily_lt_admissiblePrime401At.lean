-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_lt_admissiblePrime401At
-- name    : QEC.Coding.BalancedProduct.LPSFamily.lt_admissiblePrime401At
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:43:01.522356+00:00
-- url     : https://prove2.me/theorems/005ac32d-4bef-498b-9ff6-6b3b809153e7
-- title:
--   LPSFamily: lt admissible Prime401 At
-- statement:
--   The LPSFamily construction uses the lt admissible Prime401 At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L74-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L74-L76

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

theorem QEC.Coding.BalancedProduct.LPSFamily.lt_admissiblePrime401At (B : Nat) :
    B < (admissiblePrime401At B).q := by sorry
