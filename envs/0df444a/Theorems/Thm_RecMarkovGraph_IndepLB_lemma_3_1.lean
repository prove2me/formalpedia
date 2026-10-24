-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_3_1
-- name    : RecMarkovGraph.IndepLB.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:35.579854+00:00
-- url     : https://prove2.me/theorems/91d0abd9-1d81-4349-b199-b3a5840a80c9
-- title:
--   Lemma 3.1, p. 8 — the edge marginals of G^r_{n,p} satisfy p^i_j = p^i_{j−1}(1 − γ p^i_{j−1})
-- statement:
--   Let $p\in(0,1]$, $r\in(0,1)$ and $\gamma=1-r$. In $G^r_{n,p}$ write $p^i_j=\mathbb P\{X^i_j=1\}$ for the probability that the edge $(v_j,v_i)$ is present, $1\le j<i\le n$. Then for every $2\le j\le i-1$,
--   $$p^i_j=p^i_{j-1}\bigl[1-\gamma\,p^i_{j-1}\bigr].$$
--
--   So along each row the edge probabilities follow the recursion (3) with $a=\gamma$ started at $p^i_1=p$. This is the bridge from the random graph to Lemmas 4.2 and 4.3, and it certifies that the law of the mission obeys the conditional probabilities of Definition 1.
--
--   Differences from the source:
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: 2 ⩽ j ⩽ i − 1 (1-based) → i j : Fin n with 1 ≤ j and j < i (0-based); p^i_{j−1} is the marginal of G.Adj ⟨j − 1, _⟩ i; reason: index shift v_k = k − 1
--   - encoding: γ := 1 − r (display (1), p. 4); log is the natural log → (1 − r) written out; Real.log of the cast (n : ℝ); reason: notation only
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 8, Lemma 3.1

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

theorem lemma_3_1 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) (i j : Fin n) (hj : 1 ≤ (j : ℕ)) (hji : j < i) :
    rmrgProb n p r (fun G => G.Adj j i) =
      rmrgProb n p r (fun G => G.Adj ⟨(j : ℕ) - 1, by omega⟩ i) *
        (1 - (1 - r) * rmrgProb n p r (fun G => G.Adj ⟨(j : ℕ) - 1, by omega⟩ i)) := by sorry

end RecMarkovGraph.IndepLB
