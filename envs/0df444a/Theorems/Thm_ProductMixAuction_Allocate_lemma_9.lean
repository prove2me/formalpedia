-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_9
-- name    : ProductMixAuction.Allocate.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:37.485444+00:00
-- url     : https://prove2.me/theorems/df28dda5-cfaa-4eb8-8861-7d86d64fb4d8
-- title:
--   Lemma 9, p. 16 — δ-validity and surplus gaps of at least ε give ε/2-validity
-- statement:
--   Let $\mathcal B$ be a bid list and $p$ a price. For a bid $b$ demanding the goods $I=\arg\max_{i\in[n]_0}(b_i-p_i)\neq[n]_0$, its *surplus gap* at $p$ is $\max_{i\in[n]_0}(b_i-p_i)-\max_{i\in[n]_0\setminus I}(b_i-p_i)$. If $\mathcal B$ is $\delta$-valid at $p$ for some $\delta>0$ and every bid of $\mathcal B$ has surplus gap at least $\varepsilon$ at $p$, then
--   $$f_{\mathcal B}\ \text{is convex on}\ B(p;\varepsilon/2),$$
--   i.e. $\mathcal B$ is $\varepsilon/2$-valid at $p$.
--
--   The lemma turns a qualitative local validity into a quantitative radius, which the analysis of the shift (Lemma 13) and of the projection (Lemma 16) needs.
--
--   Differences from the source:
--   - reading: all bids in ℬ have a surplus gap of at least ε (the gap is defined only when I ≠ [n]₀) → every good not demanded by b at p has surplus at most the maximum minus ε; a bid demanding all of [n]₀ satisfies this vacuously; reason: bids demanding every good have no gap and impose no constraint, as in the proof of Lemma 13
--   - generalization: ε implicitly positive → ε any real number; reason: for ε ≤ 0 the ball B(p; ε/2) is empty and the statement holds trivially; for ε > 0 it is the paper's
--   - generalization: bid vectors integral (§2.2, p. 9) or in ℤ + {0, 1/10} (Definition 4) with reject entry b₀ = 0 → arbitrary real bid vectors over [n]₀, the reject entry v 0 unconstrained; reason: the proof never uses integrality; a bid with reject entry c has the same demanded goods as b − c·e^{[n]₀} and adds the constant w(b)·c to f_ℬ, so the statement for b₀ = c is the statement for b₀ = 0; the paper's bids are instances
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 16, Lemma 9

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Setting

namespace ProductMixAuction.Allocate

theorem lemma_9 {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) (δ ε : ℝ) (hδ : 0 < δ)
    (hB : EpsValid B p δ)
    (hgap : ∀ b ∈ B, ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - ε) :
    EpsValid B p (ε / 2) := by sorry

end ProductMixAuction.Allocate
