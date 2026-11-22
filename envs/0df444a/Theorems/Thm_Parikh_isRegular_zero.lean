-- Prove2me | Theorems.Thm_Parikh_isRegular_zero
-- name    : Parikh.isRegular_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:49.007262+00:00
-- url     : https://prove2.me/theorems/15cb968e-eada-4af0-a8fc-e15d8426f7b9
-- title:
--   Parikh: is Regular zero
-- statement:
--   A one-state rejecting NFA suffices for the empty language.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L93-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L93-L98

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

theorem Parikh.isRegular_zero : (0 : Language T).IsRegular := by sorry
