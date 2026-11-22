-- Prove2me | Theorems.Thm_UlmsTheorem_pOrder_pos_of_ne_zero
-- name    : UlmsTheorem.pOrder_pos_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:21.875111+00:00
-- url     : https://prove2.me/theorems/23470614-ce85-4014-98ba-1aa3b0d5fb7e
-- title:
--   Ulms Theorem: p Order pos of ne zero
-- statement:
--   The Ulms Theorem construction uses the p Order pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L252-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L252-L258

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

theorem UlmsTheorem.pOrder_pos_of_ne_zero (x : G) (hx : x ≠ 0) :
    0 < pOrder p x := by sorry
