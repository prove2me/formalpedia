-- Prove2me | Theorems.Thm_UlmsTheorem_coe_le_ulmHeight_of_mem
-- name    : UlmsTheorem.coe_le_ulmHeight_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:06.585897+00:00
-- url     : https://prove2.me/theorems/687a920a-4a73-4d3b-8505-76695f94a9f9
-- title:
--   Ulms Theorem: coe le ulm Height of mem
-- statement:
--   Membership in `G_α` gives the corresponding lower bound on Ulm height.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L51-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L51-L54

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

theorem UlmsTheorem.coe_le_ulmHeight_of_mem (x : G) (α : Ordinal.{0})
    (hx : x ∈ ulmSubgroup p α (G := G)) :
    (α : WithTop Ordinal.{0}) ≤ ulmHeight p x := by sorry
