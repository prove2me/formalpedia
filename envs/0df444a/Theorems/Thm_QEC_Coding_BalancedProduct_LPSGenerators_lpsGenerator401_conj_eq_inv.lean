-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGenerator401_conj_eq_inv
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerator401_conj_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:52:39.538728+00:00
-- url     : https://prove2.me/theorems/b41a8519-35ab-4b62-b9ed-7efd88ef6def
-- title:
--   LPSGenerators: lps Generator401 conj eq inv
-- statement:
--   The LPSGenerators construction uses the lps Generator401 conj eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L350-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L350-L372

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerator401_conj_eq_inv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    lpsGenerator401 q hq t.conj
        ((ShellIndex401.conj_mem_shell401_iff t).mpr ht) =
      (lpsGenerator401 q hq t ht)⁻¹ := by sorry
