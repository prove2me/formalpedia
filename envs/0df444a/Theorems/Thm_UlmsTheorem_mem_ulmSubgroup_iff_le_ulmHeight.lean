-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_iff_le_ulmHeight
-- name    : UlmsTheorem.mem_ulmSubgroup_iff_le_ulmHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:15.620336+00:00
-- url     : https://prove2.me/theorems/3cfc8ce6-bde0-4c2a-854a-e1f148bf7c61
-- title:
--   Ulms Theorem: mem ulm Subgroup iff le ulm Height
-- statement:
--   Membership in the filtration and a lower bound on the Ulm height are the same
--   statement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L99-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L99-L101

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

theorem UlmsTheorem.mem_ulmSubgroup_iff_le_ulmHeight (x : G) (γ : Ordinal.{0}) :
    x ∈ ulmSubgroup p γ (G := G) ↔ (γ : WithTop Ordinal.{0}) ≤ ulmHeight p x := by sorry
