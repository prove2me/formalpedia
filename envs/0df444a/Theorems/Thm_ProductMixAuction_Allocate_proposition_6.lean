-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_proposition_6
-- name    : ProductMixAuction.Allocate.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:34.522591+00:00
-- url     : https://prove2.me/theorems/39434432-59ab-40b7-9996-39a8ca27f5c4
-- title:
--   Proposition 6 (read for every bid list), p. 15 — f_B is convex on B(p; ε) iff no marginal weights sum to a negative number
-- statement:
--   Let $\mathcal B$ be a list of bids over the goods $[n]_0$, let $p\in\mathbb R^n$ and $\varepsilon>0$, and let $P=B(p;\varepsilon)$ be the open $L^\infty$-ball. The following are equivalent:
--
--   1. the indirect utility function $f_{\mathcal B}$ restricted to $P$ is convex;
--   2. there is no price $q\in P$ and pair of distinct goods $i,i'\in[n]_0$ at which the weights of the bids $b\in\mathcal B$ demanding both $i$ and $i'$ sum to a negative number:
--   $$\neg\,\exists\,q\in P,\ i\neq i':\quad\sum_{b\in\mathcal B:\ i,i'\in\arg\max_k(b_k-q_k)}w(b)<0 .$$
--
--   This is the local form of the validity criterion of Theorem 1; it is how the later lemmas check that removing or modifying bids keeps a list locally valid.
--
--   Differences from the source:
--   - reading: Let ℬ be an ε-valid bid list at p (which is clause 1 itself) → the equivalence 1 ⇔ 2 for every bid list ℬ, every p and every ε > 0; reason: read literally the hypothesis makes the equivalence collapse; the proof of Theorem 1 (p. 31) applies it to arbitrary ℬ
--   - generalization: bid vectors integral (§2.2, p. 9) or in ℤ + {0, 1/10} (Definition 4) with reject entry b₀ = 0 → arbitrary real bid vectors over [n]₀, the reject entry v 0 unconstrained; reason: the proof never uses integrality; a bid with reject entry c has the same demanded goods as b − c·e^{[n]₀} and adds the constant w(b)·c to f_ℬ, so the statement for b₀ = c is the statement for b₀ = 0; the paper's bids are instances
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 15, Proposition 6

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Setting

namespace ProductMixAuction.Allocate

theorem proposition_6 {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    EpsValid B p ε ↔
      ¬ ∃ q ∈ Metric.ball p ε, ∃ i i' : Fin (n + 1), i ≠ i' ∧
        ((B.filter fun b => i ∈ demGoods b q ∧ i' ∈ demGoods b q).map Bid.w).sum < 0 := by sorry

end ProductMixAuction.Allocate
