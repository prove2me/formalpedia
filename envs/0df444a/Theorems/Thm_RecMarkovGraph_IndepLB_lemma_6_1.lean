-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_6_1
-- name    : RecMarkovGraph.IndepLB.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:28.951303+00:00
-- url     : https://prove2.me/theorems/14958713-922c-4efc-8cce-38072d66312d
-- title:
--   Lemma 6.1, p. 15 — ℓ_j(γp)/γ ≤ p^i_j < min{p^i_{j−1}, 1/(γj)}
-- statement:
--   Let $p\in(0,1]$, $r\in(0,1)$, $\gamma=1-r$, and let $p^i_j$ be the probability that the edge $(v_j,v_i)$ is present in $G^r_{n,p}$. For every $2\le j\le i-1$,
--   $$\frac{\ell_j(\gamma p)}{\gamma}\ \le\ p^i_j\ <\ \min\Bigl\{p^i_{j-1},\ \frac{1}{\gamma j}\Bigr\},$$
--   with $\ell_j$ the function of display (4).
--
--   Edge probabilities therefore decay like $1/(\gamma j)$ along each row, which is what makes the graph sparse with average degree of order $\log n$.
--
--   Differences from the source:
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: 2 ⩽ j ⩽ i − 1 (1-based), ℓ_j and 1/(γj) with the paper's j → 1 ≤ j < i in Fin n (0-based j′ = j − 1); ell (j′ + 1) and 1/((1 − r)(j′ + 1)); reason: index shift v_k = k − 1
--   - encoding: γ := 1 − r (display (1), p. 4); log is the natural log → (1 − r) written out; Real.log of the cast (n : ℝ); reason: notation only
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 15, Lemma 6.1

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

theorem lemma_6_1 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) (i j : Fin n) (hj : 1 ≤ (j : ℕ)) (hji : j < i) :
    ell ((j : ℕ) + 1) ((1 - r) * p) / (1 - r) ≤ rmrgProb n p r (fun G => G.Adj j i) ∧
    rmrgProb n p r (fun G => G.Adj j i) <
      min (rmrgProb n p r (fun G => G.Adj ⟨(j : ℕ) - 1, by omega⟩ i))
        (1 / ((1 - r) * ((j : ℕ) + 1 : ℝ))) := by sorry

end RecMarkovGraph.IndepLB
