-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_theorem_4
-- name    : ProductMixAuction.Allocate.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:40.475431+00:00
-- url     : https://prove2.me/theorems/16bdcfe4-a653-4877-995a-21469a9951a0
-- title:
--   Theorem 4 (for valid bid lists), p. 12 — the target bundle splits into bundles each bidder demands at a market-clearing price
-- statement:
--   Let $J$ be a finite set of bidders, and let each bidder $j$ submit a valid list $\mathcal B^j$ of integral bids with weights $\pm1$. Let $\mathcal B$ be the aggregate list (the concatenation of the $\mathcal B^j$), $p\in\mathbb R^n$ a price and $t\in\mathbb Z^n$ a target bundle that $\mathcal B$ demands at $p$, i.e. $t\in D_{\mathcal B}(p)$ ($p$ is market-clearing for $t$). Then there is a partition
--   $$t=\sum_{j\in J}t^j\qquad\text{with}\qquad t^j\in D_{\mathcal B^j}(p)\ \text{for every}\ j\in J .$$
--
--   This guarantees that the allocation problem has a solution, so the initial problem of ALLOCATE satisfies Definition 4.
--
--   Differences from the source:
--   - reading: each bidder j has a strong-substitutes demand correspondence Dʲ, and p is market-clearing for t → each bidder has a valid integral bid list ℬʲ with demand D_{ℬʲ}, and t ∈ D_ℬ(p) for the concatenated list ℬ; reason: the proof of Theorem 19 uses the theorem in this form, through D_{ℬʲ} = D_{uʲ} (Theorem 1) and aggregate demand D_ℬ; valid bid lists are the paper's representation of strong-substitutes valuations
--   - encoding: bundles in ℤⁿ → D_ℬ(p) over [n]₀ with the reject coordinate dropped (demandN); reason: the reject coordinate is determined by the others
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 12, Theorem 4

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Setting

namespace ProductMixAuction.Allocate

theorem theorem_4 {n : ℕ} {J : Type*} [Fintype J] (B : J → List (IntBid n))
    (hw : ∀ j, ∀ b ∈ B j, b.w = 1 ∨ b.w = -1)
    (hvalid : ∀ j, Valid ((B j).map IntBid.toBid))
    (p : Fin n → ℝ) (t : Fin n → ℤ)
    (hclear : t ∈ demandN (aggregate fun j => (B j).map IntBid.toBid) p) :
    ∃ tj : J → Fin n → ℤ, ∑ j, tj j = t ∧ ∀ j, tj j ∈ demandN ((B j).map IntBid.toBid) p := by sorry

end ProductMixAuction.Allocate
