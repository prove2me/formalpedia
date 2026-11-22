-- Prove2me | Theorems.Thm_UlmsTheorem_IsPure_bot
-- name    : UlmsTheorem.IsPure_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:21.957688+00:00
-- url     : https://prove2.me/theorems/4d43b81f-121e-4598-801f-680c17bb338c
-- title:
--   Ulms Theorem: Is Pure bot
-- statement:
--   The Ulms Theorem construction uses the Is Pure bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L272-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L272-L273

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

theorem UlmsTheorem.IsPure_bot : IsPure p (⊥ : AddSubgroup G) := by sorry
