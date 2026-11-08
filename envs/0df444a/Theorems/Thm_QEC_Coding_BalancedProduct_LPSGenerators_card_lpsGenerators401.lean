-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_card_lpsGenerators401
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.card_lpsGenerators401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:45.703812+00:00
-- url     : https://prove2.me/theorems/302ca8e2-88d4-431f-9e44-4b0ab7f533bb
-- title:
--   LPSGenerators: card lps Generators401
-- statement:
--   The LPSGenerators construction uses the card lps Generators401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L468-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L468-L476

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic

theorem QEC.Coding.BalancedProduct.LPSGenerators.card_lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    (lpsGenerators401 q hq).card = 402 := by sorry
