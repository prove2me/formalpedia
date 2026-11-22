-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_zsmul_iff_of_pSocle
-- name    : UlmsTheorem.mem_ulmSubgroup_zsmul_iff_of_pSocle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:32.108691+00:00
-- url     : https://prove2.me/theorems/332d88c9-7a3a-44d2-a8ec-5c18eae01a3a
-- title:
--   Ulms Theorem: mem ulm Subgroup zsmul iff of p Socle
-- statement:
--   For an element `g` of the `p`-socle (`p • g = 0`), membership of `n • g` in a
--   Ulm subgroup is equivalent to membership of `g`, provided `p ∤ n`.
--   Proof: Bezout gives `a * n + b * p = 1`, so `g = a • (n • g) + b • (p • g) = a • (n • g)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L379-L405
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L379-L405

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

theorem UlmsTheorem.mem_ulmSubgroup_zsmul_iff_of_pSocle [Fact p.Prime] {g : G}
    (hpg : p • g = 0) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (β : Ordinal) :
    n • g ∈ ulmSubgroup p β (G := G) ↔ g ∈ ulmSubgroup p β (G := G) := by sorry
