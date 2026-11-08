-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_not_projectiveDetIsSquare_of_mem_lpsGenerators401
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.not_projectiveDetIsSquare_of_mem_lpsGenerators401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:26.912191+00:00
-- url     : https://prove2.me/theorems/6435a04a-c787-4961-b281-d1f3c5561d2b
-- title:
--   LPSGenerators: not projective Det Is Square of mem lps Generators401
-- statement:
--   The LPSGenerators construction uses the not projective Det Is Square of mem lps Generators401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L488-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L488-L495

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.not_projectiveDetIsSquare_of_mem_lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq) :
    ¬ ProjectiveDetIsSquare s := by sorry
