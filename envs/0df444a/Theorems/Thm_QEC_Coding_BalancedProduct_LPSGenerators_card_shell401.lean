-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_card_shell401
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.card_shell401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:20.359417+00:00
-- url     : https://prove2.me/theorems/7a21a36c-597c-445a-97b2-6031160438ed
-- title:
--   LPSGenerators: card shell401
-- statement:
--   The LPSGenerators construction uses the card shell401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L129-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L129-L134

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.card_shell401 : shell401.card = 402 := by sorry
