-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsMatrix401_mul_conj
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.lpsMatrix401_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:24.357365+00:00
-- url     : https://prove2.me/theorems/7f852b98-97f5-44d5-bc14-1ae7a030b4e0
-- title:
--   LPSGenerators: lps Matrix401 mul conj
-- statement:
--   The LPSGenerators construction uses the lps Matrix401 mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L302-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L302-L307

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.lpsMatrix401_mul_conj
    (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) (ht : t ∈ shell401) :
    lpsMatrix401 q t * lpsMatrix401 q t.conj =
      (401 : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by sorry
