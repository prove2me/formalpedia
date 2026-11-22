-- Prove2me | Theorems.Thm_Parikh_isRegular_one
-- name    : Parikh.isRegular_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:49.982184+00:00
-- url     : https://prove2.me/theorems/f3efae25-f498-48a3-833f-bcdc50fe5f60
-- title:
--   Parikh: is Regular one
-- statement:
--   A one-state accepting NFA with no transitions recognizes epsilon.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L101-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/WordBlockAutomata.lean#L101-L106

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

theorem Parikh.isRegular_one : (1 : Language T).IsRegular := by sorry
