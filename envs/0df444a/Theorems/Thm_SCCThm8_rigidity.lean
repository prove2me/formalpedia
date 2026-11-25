-- Prove2me | Theorems.Thm_SCCThm8_rigidity
-- name    : SCCThm8.rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:43.787364+00:00
-- url     : https://prove2.me/theorems/0b88f53b-609b-41ce-8946-e26878103994
-- title:
--   SCCThm8: rigidity
-- statement:
--   **Rigidity (non-abelian).** Let `k ≥ 2`. Suppose `f₁ A * f₂ B * f₃ C = 1` whenever `A, B, C` are
--   pairwise disjoint `k`-subsets of `Fin (3k)`. Then there are pairwise commuting `gᵢ` such that,
--   for every triple of `k`-subsets, `f₁ A * f₂ B * f₃ C = ∏ᵢ gᵢ ^ (mult A B C i - 1)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L373-L409
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L373-L409

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.rigidity {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C = psi g (fun i => mult A B C i - 1) := by sorry
