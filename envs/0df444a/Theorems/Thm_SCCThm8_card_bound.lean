-- Prove2me | Theorems.Thm_SCCThm8_card_bound
-- name    : SCCThm8.card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:06.520249+00:00
-- url     : https://prove2.me/theorems/d129094d-0932-5649-b6cf-3c1fe91198ab
-- title:
--   SCCThm8: card bound
-- statement:
--   **Counting (Theorem 3, via the lift lemma).** Let the `gᵢ` commute pairwise, and suppose
--   `∏ gᵢ^eᵢ ≠ 1` for every nonzero `e ∈ {-1,0,1,2}^n` with `∑ e = 0`. Then `|G| ≥ 2^(n-1)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L208-L273
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L208-L273

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.card_bound {G : Type*} [Group G] [Fintype G] {n : ℕ} (hn : 1 ≤ n) (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j))
    (hE : ∀ e : Fin n → ℤ, (∀ i, -1 ≤ e i ∧ e i ≤ 2) → ∑ i, e i = 0 → e ≠ 0 → psi g e ≠ 1) :
    2 ^ (n - 1) ≤ Fintype.card G := by sorry
