-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_13
-- name    : ProductMixAuction.Allocate.lemma_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:05.999344+00:00
-- url     : https://prove2.me/theorems/5288b252-98cb-4bf6-ac84-5ea2268d3b06
-- title:
--   Lemma 13, p. 21 — shifting one bidder's integral bids by |ε| < 1/4 keeps local validity and shrinks demand
-- statement:
--   Fix $\varepsilon$ with $|\varepsilon|<\tfrac14$, a good $i\in[n]$ and a bidder $j\in J$. Let $\mathcal A$ be an allocation problem with integral bids and an integral price $p$, and let $\mathcal A'$ be obtained by replacing $\mathcal B^j$ with
--   $$(\mathcal B^j)'=\{b+\varepsilon e^i\ :\ b\in\mathcal B^j\}.$$
--   Then for every price $p^\varepsilon$ with $\|p^\varepsilon-p\|_\infty\le|\varepsilon|$ (in particular every $p^\varepsilon\in B(p,\varepsilon)$ and every $p^\varepsilon\in\{p\pm\varepsilon e^S: S\subseteq[n]\}$) and every bidder $j'$:
--
--   1. the bid list of $j'$ in $\mathcal A'$ is locally valid at $p^\varepsilon$;
--   2. the bundles $j'$ demands at $p^\varepsilon$ in $\mathcal A'$ form a subset of the bundles $j'$ demands at $p$ in $\mathcal A$.
--
--   This is the first half of the correctness of ShiftProjectUnshift: a small shift of one bidder followed by a small price change never creates new demand.
--
--   Differences from the source:
--   - generalization: any price p^ε ∈ B(p, ε), the open L∞-ball, with ε possibly negative (|ε| < 1/4) → p^ε in the closed L∞-ball of radius |ε|; reason: the radius |ε| is the only meaningful radius for negative ε, and the closed ball contains the printed open ball and also the candidates p ± εe^S of Proposition 14, at which the proof of Lemma 18 (p. 22) applies this lemma; the proof (surplus gaps ≥ 1, distances ≤ 2|ε| < 1/2) covers the closed ball unchanged
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 21, Lemma 13

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_13 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (ε : ℝ) (hε : |ε| < 1 / 4) (i : Fin n) (j : J) :
    ∀ q ∈ Metric.closedBall A.p |ε|, ∀ j' : J,
      LocallyValid (shiftList A.B j i.succ ε j') q ∧
        demand (shiftList A.B j i.succ ε j') q ⊆ demand (A.B j') A.p := by sorry

end ProductMixAuction.Allocate
