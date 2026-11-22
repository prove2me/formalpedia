-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_zsmul_iff
-- name    : UlmsTheorem.mem_ulmSubgroup_zsmul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:14.939408+00:00
-- url     : https://prove2.me/theorems/f05aac2a-0551-4b44-987c-6eed3c6f4663
-- title:
--   Ulms Theorem: mem ulm Subgroup zsmul iff
-- statement:
--   **Multiplication by an integer prime to `p` preserves the filtration.**
--
--   In a primary group every element has `p`-power order, so an `n` prime to `p` is
--   invertible on it: Bezout gives `a·n + b·p^k = 1` with `p^k • u = 0`, whence
--   `u = a • (n • u)`.  Membership of `n • u` and of `u` therefore agree at every
--   level.
--
--   This generalizes `mem_ulmSubgroup_zsmul_iff_of_pSocle` off the socle, which is
--   what the one-line extension step needs: the challenge element is a socle element,
--   but the elements `b + r·x` it must be checked against are not.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L334-L364
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L334-L364

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

theorem UlmsTheorem.mem_ulmSubgroup_zsmul_iff [Fact p.Prime] (hprim : IsPrimaryPGroup p G)
    {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (u : G) (β : Ordinal.{0}) :
    n • u ∈ ulmSubgroup p β (G := G) ↔ u ∈ ulmSubgroup p β (G := G) := by sorry
