-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsMatrix401_conj
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.lpsMatrix401_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:53:11.782198+00:00
-- url     : https://prove2.me/theorems/914d150e-96df-40f2-9270-e87cb22893e5
-- title:
--   LPSGenerators: lps Matrix401 conj
-- statement:
--   The LPSGenerators construction uses the lps Matrix401 conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L198-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L198-L203

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.lpsMatrix401_conj
    (q : ℕ) [Fact q.Prime] (t : ShellIndex401) :
    lpsMatrix401 q t.conj = (lpsMatrix401 q t).adjugate := by sorry
