-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_eq_11
-- name    : RecMarkovGraph.IndepLB.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:11.304746+00:00
-- url     : https://prove2.me/theorems/9d0545d4-d62d-4258-b3a6-3c6f8df41772
-- title:
--   (11), proof of Theorem 2.1, p. 14 — for n > e^{γ/(ε−ε₀)}, P{α ≥ n/((2+ε)/γ·log n)} ≥ P{α ≥ n/((2+ε₀)/γ·log n + 1)} ≥ P{d/log n ≤ (2+ε₀)/γ}
-- statement:
--   Let $p\in(0,1]$, $r\in(0,1)$, $\gamma=1-r$, and fix $\varepsilon>\varepsilon_0>0$. For every $n>e^{\gamma/(\varepsilon-\varepsilon_0)}$,
--   $$\mathbb P\Bigl\{\alpha(G^r_{n,p})\ge\frac{n}{\frac{2+\varepsilon}{\gamma}\log n}\Bigr\}\ \ge\ \mathbb P\Bigl\{\alpha(G^r_{n,p})\ge\frac{n}{\frac{2+\varepsilon_0}{\gamma}\log n+1}\Bigr\}\ \ge\ \mathbb P\Bigl\{\frac{d(G^r_{n,p})}{\log n}\le\frac{2+\varepsilon_0}{\gamma}\Bigr\}.$$
--
--   Together with Theorem 2.2, which sends the right-hand side to $1$, this display proves the goal.
--
--   Differences from the source:
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: "if n is sufficiently large", made explicit on the page as n > e^{γ/(ε−ε_0)} → hypothesis Real.exp ((1 − r)/(ε − ε₀)) < n; reason: the page's own threshold; not weakened to an eventual statement
--   - encoding: γ := 1 − r (display (1), p. 4); log is the natural log → (1 − r) written out; Real.log of the cast (n : ℝ); reason: notation only
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 14, display (11) in the proof of Theorem 2.1

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

theorem eq_11 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (ε ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀ε : ε₀ < ε) (n : ℕ)
    (hn : Real.exp ((1 - r) / (ε - ε₀)) < (n : ℝ)) :
    rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε₀) / (1 - r) * Real.log n + 1) ≤ (G.indepNum : ℝ)) ≤
      rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε) / (1 - r) * Real.log n) ≤ (G.indepNum : ℝ)) ∧
    rmrgProb n p r (fun G => avgDeg G / Real.log n ≤ (2 + ε₀) / (1 - r)) ≤
      rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε₀) / (1 - r) * Real.log n + 1) ≤ (G.indepNum : ℝ)) := by sorry

end RecMarkovGraph.IndepLB
