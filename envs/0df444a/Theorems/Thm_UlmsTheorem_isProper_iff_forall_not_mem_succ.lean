-- Prove2me | Theorems.Thm_UlmsTheorem_isProper_iff_forall_not_mem_succ
-- name    : UlmsTheorem.isProper_iff_forall_not_mem_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:06.890043+00:00
-- url     : https://prove2.me/theorems/0db7cbdd-53c1-4dd8-ac48-18bb597fa8fc
-- title:
--   Ulms Theorem: is Proper iff forall not mem succ
-- statement:
--   For an element of exact height `α`, properness over `S` says exactly that no
--   `S`-translate reaches `G_(α+1)`.
--
--   Both Kaplansky target constructions establish properness by ruling out a higher
--   translate and consume it the same way, so this is the form they share.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L115-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L115-L127

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

theorem UlmsTheorem.isProper_iff_forall_not_mem_succ (S : AddSubgroup G) {x : G}
    {α : Ordinal.{0}} (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    IsProper p S x ↔ ∀ c : S, x + (c : G) ∉ ulmSubgroup p (Order.succ α) (G := G) := by sorry
