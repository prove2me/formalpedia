-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_not_projectiveDetIsSquare_lpsGenerator401
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.not_projectiveDetIsSquare_lpsGenerator401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:27.047199+00:00
-- url     : https://prove2.me/theorems/8e6f7dfc-8786-41f8-a053-ce711d6a3fad
-- title:
--   LPSGenerators: not projective Det Is Square lps Generator401
-- statement:
--   The LPSGenerators construction uses the not projective Det Is Square lps Generator401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L342-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L342-L348

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.not_projectiveDetIsSquare_lpsGenerator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    ¬ ProjectiveDetIsSquare (lpsGenerator401 q hq t ht) := by sorry
