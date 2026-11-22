-- Prove2me | Theorems.Thm_UlmsTheorem_not_mem_of_mem_of_not_mem_add
-- name    : UlmsTheorem.not_mem_of_mem_of_not_mem_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:25.925921+00:00
-- url     : https://prove2.me/theorems/aa4d2836-342c-447d-ac3c-4d6e0d2c0dfb
-- title:
--   Ulms Theorem: not mem of mem of not mem add
-- statement:
--   If `a` is in a subgroup but `b` is not, their sum is not in the subgroup.
--   Useful for the ultrametric argument in the extension theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L320-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L320-L322

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

theorem UlmsTheorem.not_mem_of_mem_of_not_mem_add {S : AddSubgroup G} {a b : G}
    (ha : a ∈ S) (hb : b ∉ S) : a + b ∉ S := by sorry
