-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_mem_lpsGenerators401_iff
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.mem_lpsGenerators401_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:19.481822+00:00
-- url     : https://prove2.me/theorems/8e0d676b-b10e-4938-b977-77abcdfd109d
-- title:
--   LPSGenerators: mem lps Generators401 iff
-- statement:
--   The LPSGenerators construction uses the mem lps Generators401 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L478-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L478-L486

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.mem_lpsGenerators401_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (s : PGL(2, ZMod q)) :
    s ∈ lpsGenerators401 q hq ↔
      ∃ t : ShellIndex401, ∃ ht : t ∈ shell401,
        lpsGenerator401 q hq t ht = s := by sorry
