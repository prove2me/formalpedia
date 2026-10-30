-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_theorem_2_1
-- name    : RecMarkovGraph.IndepLB.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:08.134821+00:00
-- url     : https://prove2.me/theorems/51790111-2e2e-4d77-81cb-8997e4a77e5b
-- title:
--   Theorem 2.1, p. 4 — for r < 1, w.h.p. α(G^r_{n,p}) ≥ ((1 − r)/(2 + ε))·n/log n for every ε > 0
-- statement:
--   Let $p\in(0,1]$ and $r\in(0,1)$, put $\gamma=1-r$, and let $G^r_{n,p}$ be the recursive Markov random graph on $n$ vertices. For every $\varepsilon>0$, with high probability
--   $$\alpha(G^r_{n,p})\ \ge\ \frac{\gamma}{2+\varepsilon}\,\frac{n}{\log n},$$
--   that is,
--   $$\lim_{n\to\infty}\mathbb P\Bigl\{\alpha(G^r_{n,p})\ge\frac{\gamma}{2+\varepsilon}\frac{n}{\log n}\Bigr\}=1,$$
--   where $\alpha$ is the stability number and $\log$ the natural logarithm.
--
--   This is the paper's first main result: although consecutive edges at a vertex are dependent, the graph keeps independent sets of order $n/\log n$, as the Erdős–Rényi graph with edge probability of order $\log n/n$ does.
--
--   Differences from the source:
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: "w.h.p.": P{P_n is true} → 1 as n → ∞ (p. 4) → Filter.Tendsto (fun n => rmrgProb n p r P_n) atTop (𝓝 1); reason: the paper's own definition
--   - encoding: γ := 1 − r (display (1), p. 4); log is the natural log → (1 − r) written out; Real.log of the cast (n : ℝ); reason: notation only
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 4, Theorem 2.1 (proof p. 14)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Filter Topology

theorem theorem_2_1 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => rmrgProb n p r
        (fun G => (1 - r) / (2 + ε) * ((n : ℝ) / Real.log n) ≤ (G.indepNum : ℝ)))
      atTop (𝓝 1) := by sorry

end RecMarkovGraph.IndepLB
