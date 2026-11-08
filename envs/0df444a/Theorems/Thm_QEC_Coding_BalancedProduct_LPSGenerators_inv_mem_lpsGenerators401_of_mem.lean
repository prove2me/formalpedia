-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_inv_mem_lpsGenerators401_of_mem
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.inv_mem_lpsGenerators401_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:31.098861+00:00
-- url     : https://prove2.me/theorems/91c1cdc0-3ca0-40a1-938c-260314f54af2
-- title:
--   LPSGenerators: inv mem lps Generators401 of mem
-- statement:
--   The LPSGenerators construction uses the inv mem lps Generators401 of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L497-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L497-L506

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.inv_mem_lpsGenerators401_of_mem
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq) :
    s⁻¹ ∈ lpsGenerators401 q hq := by sorry
