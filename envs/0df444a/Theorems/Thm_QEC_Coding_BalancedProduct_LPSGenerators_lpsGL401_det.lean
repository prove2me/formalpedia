-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGL401_det
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.lpsGL401_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:17.360645+00:00
-- url     : https://prove2.me/theorems/f2998b0c-f885-44c0-a5f2-e979f1a79552
-- title:
--   LPSGenerators: lps GL401 det
-- statement:
--   The LPSGenerators construction uses the lps GL401 det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L327-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L327-L333

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.lpsGL401_det
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    ((lpsGL401 q hq t ht).det : ZMod q) = (401 : ZMod q) := by sorry
