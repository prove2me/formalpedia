-- Prove2me | Theorems.Thm_SidB_chain_lower
-- name    : SidB.chain_lower
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T21:27:04.205837+00:00
-- url     : https://prove2.me/theorems/b1948eeb-8831-4737-a713-77732d31bbb2
-- title:
--   The chain lower bound (Lemma 3.4)
-- statement:
--   Lemma 3.4 of the paper: the counting step of the proof of Theorem 3.1. Let r be positive with r at most m and the copy numbers beta_k positive. Then for every graphon W, the edge density to the power q_{alpha,H} is at most the homomorphism density of the [r]-chain core hypergraph G_alpha under the weight vector q: t_{K_2}(W) ^ q_{alpha,H} <= t_{G_alpha}(W_alpha). The proof evaluates t_{G_alpha}(W_alpha) as the beta-weighted homomorphism density of the (r,r)-downset graph J, a bipartite density whose weight vector has beta_r = alpha_r positive, so that the corresponding blown-up bipartite graph has a vertex complete to the other side; the theorem of Conlon, Fox, and Sudakov then bounds the weighted density of J below by the edge density to the power e_beta(J), and the elementary binomial identity C(m,r) C(r,k) = C(m,k) C(m-k,r-k) rewrites e_beta(J) as e_alpha(H) / C(m,r) = q_{alpha,H}.
--
--   **Formalization Note** The theorem of Conlon, Fox, and Sudakov (a bipartite graph with a vertex complete to the other side satisfies Sidorenko) is the external ingredient here, recorded as proposed work; the exponent qAH is defined so that the binomial rewrite is exactly the content of the definition.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 3 (Lemma 3.4, pages 7-8), via the theorem of D. Conlon, J. Fox, B. Sudakov, An approximate version of Sidorenko's conjecture, Geom. Funct. Anal. 20(6) (2010) 1354-1366.

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 5 (Lemma 3.4): the chain lower bound. Let r be positive with
r at most m and let the copy numbers beta_k be positive. For every
graphon, the edge density to the power q_alpha,H - the weighted edge count
of the (m,r)-downset graph divided by C(m,r) - is at most the homomorphism
density of the [r]-chain core hypergraph G_alpha under the weight vector
q. The proof evaluates the G_alpha density as the beta-weighted homomorphism
density of the (r,r)-downset graph, a bipartite density with at least one
right vertex complete to the other side, to which the theorem of Conlon,
Fox, and Sudakov applies; that theorem, and the elementary binomial
identity rewriting its exponent, is the proposed work here. -/
theorem chain_lower (g : Graphon) (m r : ℕ) (β : ℕ → ℕ) (hr : 0 < r) (hmr : r ≤ m)
    (hβ : ∀ k, 1 ≤ k → k ≤ r → 0 < β k) :
    g.edgeDens ^ (qAH m r β) ≤ rDens g (gAlpha r β) (qOf r β) := by sorry

end SidB
