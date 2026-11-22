-- Prove2me | Theorems.Thm_Parikh_mem_word_mul_cons
-- name    : Parikh.mem_word_mul_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:47.259392+00:00
-- url     : https://prove2.me/theorems/6262e7d1-70c6-42d1-9472-45bf8c6c3ccb
-- title:
--   Parikh: mem word mul cons
-- statement:
--   Reading the head of a literal prefix leaves its tail as the prefix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L109-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L109-L120

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

theorem Parikh.mem_word_mul_cons (a b : T) (u x : List T) (L : Language T) :
    a :: x ∈ ({b :: u} : Language T) * L ↔
      a = b ∧ x ∈ ({u} : Language T) * L := by sorry
