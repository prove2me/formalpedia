-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_5_1
-- name    : RecMarkovGraph.IndepLB.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:06.109513+00:00
-- url     : https://prove2.me/theorems/1b91037b-74fb-4cc8-8ab0-64a1a1a9e7b7
-- title:
--   Lemma 5.1, p. 14 (Caro–Hansen–Sopena) — every graph with n vertices and m edges has α(G) ≥ max{n²/(n + 2m), (2n − m)/3}
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and $m$ edges, and let $\alpha(G)$ be its stability number, the largest size of a set of pairwise non-adjacent vertices. Then
--   $$\alpha(G)\ \ge\ \max\Bigl\{\frac{n^2}{n+2m},\ \frac{2n-m}{3}\Bigr\}.$$
--
--   The first bound equals $n/(1+d(G))$ with $d(G)=2m/n$ the average degree; it turns the concentration of the average degree (Theorem 2.2) into the lower bound on $\alpha(G^r_{n,p})$.
--
--   Differences from the source:
--   - encoding: any n-vertex graph G with m edges; α(G) → G : SimpleGraph V on a Fintype V, n = Fintype.card V, m = G.edgeFinset.card, α = SimpleGraph.indepNum, all cast to ℝ; reason: the same objects; at n = 0 both sides are 0 (Lean's 0/0 = 0)
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 14, Lemma 5.1 (citing Caro, Hansen, Sopena 2003, Theorems 10 and 11)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    max (((Fintype.card V : ℝ)) ^ 2 / ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)))
        ((2 * (Fintype.card V : ℝ) - (G.edgeFinset.card : ℝ)) / 3) ≤ (G.indepNum : ℝ) := by sorry

end RecMarkovGraph.IndepLB
