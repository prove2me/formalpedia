-- Prove2me | Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
-- name    : QEC.Coding.Why24BooleanANF.evaluate_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:11.588204+00:00
-- url     : https://prove2.me/theorems/7ec76fcf-0b4e-4862-a51a-df40d22538cc
-- title:
--   Why24 Boolean ANF: evaluate generator
-- statement:
--   The Why24 Boolean ANF construction uses the evaluate generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/BooleanANF.lean#L124-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/BooleanANF.lean#L124-L128

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24BooleanANF
open scoped BigOperators

theorem QEC.Coding.Why24BooleanANF.evaluate_generator {n : Nat} (word : Fin n → ZMod 2) (coordinate : Fin n) :
    evaluate word (generator coordinate) = word coordinate := by sorry
