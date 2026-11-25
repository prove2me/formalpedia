-- Prove2me | Theorems.Thm_SCCThm8_power_deg_card_ge
-- name    : SCCThm8.power_deg_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:54:41.609304+00:00
-- url     : https://prove2.me/theorems/7d938b19-a156-4192-9011-64a3c390c64e
-- title:
--   SCCThm8: power deg card ge
-- statement:
--   **Degeneration bound for `T_k^{⊗m}`.** Take a monomial degeneration of the group tensor of `G`
--   onto `T_k^{⊗m}`. It consists of maps `f₁, f₂, f₃` into `G` and integer weights `a, b, c` on
--   `m`-tuples of `k`-subsets of `Fin (3k)` such that:
--   * blockwise-disjoint triples have product `1` and weight `0`;
--   * every other triple with product `1` has positive weight.
--   Then `|G| ≥ C(3k, ⌊3k/2⌋)^m`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L51-L143
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L51-L143

module
public import Definitions.Def_SCCThm8_PowerRigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.power_deg_card_ge {G : Type*} [Group G] [Fintype G] (k m : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) (a b c : (Fin m → Finset (Fin (3 * k))) → ℤ)
    (hpart : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    Nat.choose (3 * k) (3 * k / 2) ^ m ≤ Fintype.card G := by sorry
