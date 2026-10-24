-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_6_2
-- name    : RecMarkovGraph.IndepLB.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:37.113487+00:00
-- url     : https://prove2.me/theorems/0b19ed16-7bb3-42f9-a4b9-32b43c4a746e
-- title:
--   Lemma 6.2, p. 15 (corrected: upper bound 1 − r p^i_{j−1} for the printed γ p^i_{j−1}) — bounds on P{X^i_j = 0 | X^i_k = 0} and P{X^i_j = 1 | X^i_k = 1}
-- statement:
--   Let $p\in(0,1]$, $r\in(0,1)$, $\gamma=1-r$, and let $p^i_{j-1}$ be the probability that the edge $(v_{j-1},v_i)$ is present in $G^r_{n,p}$. For $1\le k<j<i$,
--   $$1-p^i_{j-1}\ \le\ \mathbb P\{X^i_j=0\mid X^i_k=0\}\ \le\ 1-r\,p^i_{j-1},\qquad r\,p^i_{j-1}\ \le\ \mathbb P\{X^i_j=1\mid X^i_k=1\}\ \le\ p^i_{j-1}.$$
--
--   The second pair of bounds is what controls the joint probabilities $\mathbb P\{Y_iY_j=1\}\le p_ip_{j-1}$ in the second-moment estimate of Lemma 10.1.
--
--   Differences from the source:
--   - correction: P{X^i_j = 0 | X^i_k = 0} ⩽ γ p^i_{j−1} → P{X^i_j = 0 ∧ X^i_k = 0} ≤ (1 − r q) P{X^i_k = 0}, q = p^i_{j−1}; reason: false as printed: p = r = 1/2, k = 1, j = 2 gives P{X_2 = 0 | X_1 = 0} = 1 − p = 1/2 > γ p_1 = 1/4; the proof writes the (2,1) entry 1 − r p of (2) as γp, and with the right entry the same argument gives 1 − r p^i_{j−1}
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: conditional probabilities P{A | B}; 1 ⩽ k < j < i → c·P(B) ≤ P(A ∩ B) ≤ c′·P(B); k < j < i in Fin n; reason: the multiplicative form equals the conditional one when P(B) > 0 and avoids the undefined case P(B) = 0 (p = 1, k = 1); 0-based index shift
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 15, Lemma 6.2

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

theorem lemma_6_2 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) (i j k : Fin n) (hkj : k < j) (hji : j < i) :
    let q := rmrgProb n p r (fun G => G.Adj ⟨(j : ℕ) - 1, by omega⟩ i)
    ((1 - q) * rmrgProb n p r (fun G => ¬ G.Adj k i) ≤
        rmrgProb n p r (fun G => ¬ G.Adj j i ∧ ¬ G.Adj k i) ∧
      rmrgProb n p r (fun G => ¬ G.Adj j i ∧ ¬ G.Adj k i) ≤
        (1 - r * q) * rmrgProb n p r (fun G => ¬ G.Adj k i)) ∧
    (r * q * rmrgProb n p r (fun G => G.Adj k i) ≤
        rmrgProb n p r (fun G => G.Adj j i ∧ G.Adj k i) ∧
      rmrgProb n p r (fun G => G.Adj j i ∧ G.Adj k i) ≤
        q * rmrgProb n p r (fun G => G.Adj k i)) := by sorry

end RecMarkovGraph.IndepLB
