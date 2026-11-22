-- Prove2me | Theorems.Thm_Parikh_isRegular_word_mul
-- name    : Parikh.isRegular_word_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:51.150307+00:00
-- url     : https://prove2.me/theorems/74a9eaf0-d4eb-4103-925a-1b3ee3b19040
-- title:
--   Parikh: is Regular word mul
-- statement:
--   Prepending one fixed word preserves DFA regularity. The additional NFA
--   states are the finitely many suffixes of that word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L124-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L124-L160

module
public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
set_option autoImplicit true
@[expose] public section
public section
open scoped Computability
open Parikh
variable {T : Type*}

theorem Parikh.isRegular_word_mul (w : List T) (R : Language T) (hR : R.IsRegular) :
    (({w} : Language T) * R).IsRegular := by sorry
