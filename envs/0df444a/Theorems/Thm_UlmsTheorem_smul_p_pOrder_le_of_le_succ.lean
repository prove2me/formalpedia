-- Prove2me | Theorems.Thm_UlmsTheorem_smul_p_pOrder_le_of_le_succ
-- name    : UlmsTheorem.smul_p_pOrder_le_of_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:15.535063+00:00
-- url     : https://prove2.me/theorems/f3c74951-3670-44a7-bd04-41576fdf2150
-- title:
--   Ulms Theorem: smul p p Order le of le succ
-- statement:
--   The converse: killing `x` at level `n + 1` kills `p • x` at level `n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L212-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L212-L216

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

theorem UlmsTheorem.smul_p_pOrder_le_of_le_succ {x : G} {n : ℕ} (h : pOrder p x ≤ n + 1) :
    pOrder p (p • x) ≤ n := by sorry
