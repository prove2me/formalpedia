-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_theorem_2_2
-- name    : RecMarkovGraph.IndepLB.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:09.341746+00:00
-- url     : https://prove2.me/theorems/a0fafe84-e39c-4b8e-8d05-e91f0ef1658d
-- title:
--   Theorem 2.2, p. 4 — d(G^r_{n,p})/log n concentrates to 2/γ
-- statement:
--   Let $p\in(0,1]$, $r\in(0,1)$ and $\gamma=1-r$, and let $d(G)=2|E(G)|/n$ be the average degree. Then $d(G^r_{n,p})/\log n$ concentrates to $2/\gamma$: for every $\varepsilon>0$,
--   $$\lim_{n\to\infty}\mathbb P\Bigl\{\Bigl|\frac{d(G^r_{n,p})}{\log n}-\frac2\gamma\Bigr|\le\varepsilon\Bigr\}=1 .$$
--
--   The recursive Markov random graph is thus sparse, with average degree $(2/\gamma+o(1))\log n$ with high probability; through Lemma 5.1 this yields the goal.
--
--   Differences from the source:
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: d(G) = (1/n) Σ deg(v_i) (p. 12) → avgDeg G = 2 |E(G)| / n; reason: handshake lemma; same number
--   - encoding: ξ_n concentrates to c: P{|ξ_n − c| ⩽ ε} → 1 for every ε > 0 (p. 4) → ∀ ε > 0, Tendsto (fun n => P{|ξ_n − c| ≤ ε}) atTop (𝓝 1); reason: the paper's own definition, with ≤ ε
--   - encoding: γ := 1 − r (display (1), p. 4); log is the natural log → (1 − r) written out; Real.log of the cast (n : ℝ); reason: notation only
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 4, Theorem 2.2 (proof §5.1, pp. 12–14)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Filter Topology

theorem theorem_2_2 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
          rmrgProb n p r (fun G => |avgDeg G / Real.log n - 2 / (1 - r)| ≤ ε)) atTop (𝓝 1) := by sorry

end RecMarkovGraph.IndepLB
