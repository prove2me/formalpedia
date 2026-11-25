-- Prove2me | Theorems.Thm_SCCThm8_deg_card_ge
-- name    : SCCThm8.deg_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:56.438914+00:00
-- url     : https://prove2.me/theorems/b47f7a6a-749b-4f03-9efb-3a800885b8ad
-- title:
--   SCCThm8: deg card ge
-- statement:
--   **Degeneration bound.** Take a monomial (Strassen combinatorial) degeneration of the group
--   tensor of `G` onto `T_k`. It consists of maps `f₁, f₂, f₃` into `G` and integer weights `a, b, c`
--   on `k`-subsets of `Fin (3k)` such that:
--   * partitions (pairwise disjoint triples) have product `1` and weight `0`;
--   * every other triple with product `1` has strictly positive weight.
--   Then `|G| ≥ C(3k, ⌊3k/2⌋)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean#L52-L133
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean#L52-L133

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.deg_card_ge {G : Type*} [Group G] [Fintype G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G) (a b c : Finset (Fin (3 * k)) → ℤ)
    (hpart : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      ¬ (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    Nat.choose (3 * k) (3 * k / 2) ≤ Fintype.card G := by sorry
