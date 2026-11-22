-- Prove2me | Theorems.Thm_UlmsTheorem_ulmHeight_eq_of_mem_not_mem_succ
-- name    : UlmsTheorem.ulmHeight_eq_of_mem_not_mem_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:09.453665+00:00
-- url     : https://prove2.me/theorems/a02023d1-9970-4429-800a-6e65b63c8ba4
-- title:
--   Ulms Theorem: ulm Height eq of mem not mem succ
-- statement:
--   An element in `G_α` but not `G_(α+1)` has Ulm height exactly `α`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L104-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L104-L108

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

theorem UlmsTheorem.ulmHeight_eq_of_mem_not_mem_succ (x : G) (α : Ordinal.{0})
    (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    ulmHeight p x = (α : WithTop Ordinal.{0}) := by sorry
