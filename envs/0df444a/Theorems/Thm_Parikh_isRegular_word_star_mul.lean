-- Prove2me | Theorems.Thm_Parikh_isRegular_word_star_mul
-- name    : Parikh.isRegular_word_star_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:50.251813+00:00
-- url     : https://prove2.me/theorems/53767fb2-fcd9-4273-b605-b2d7d008fb17
-- title:
--   Parikh: is Regular word star mul
-- statement:
--   Prepending any number of copies of one fixed word preserves DFA regularity.
--   Suffix states return to the same starred prefix; transitions may also enter the
--   continuation DFA. The empty repeated word is handled without epsilon loops.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L165-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L165-L225

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

theorem Parikh.isRegular_word_star_mul (w : List T) (R : Language T) (hR : R.IsRegular) :
    (({w} : Language T)∗ * R).IsRegular := by sorry
