-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_3_2
-- name    : RecMarkovGraph.IndepLB.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:37.857178+00:00
-- url     : https://prove2.me/theorems/c85fa983-402d-4a1f-a70c-8e33bc50f0ac
-- title:
--   Lemma 3.2, pp. 8–9 — the first i − 1 edges of every later row, and the first i − 1 terms of the decay chain, have the law of row i
-- statement:
--   Let $p\in(0,1]$, $r\in(0,1)$.
--
--   1. In $G^r_{n,p}$, for $2\le i<j\le n$, the chain $(X^j_1,\dots,X^j_{i-1})$ of the first $i-1$ edges of vertex $v_j$ has the same joint law as the chain $(X^i_1,\dots,X^i_{i-1})$ of vertex $v_i$.
--   2. If $Y_1,Y_2,\dots$ is a Markov chain of Bernoulli variables with $\mathbb P\{Y_1=1\}=p$ and transition matrix
--   $$\mathbf P_{j-1}=\begin{pmatrix}1-p_{j-1}& p_{j-1}\\ 1-r\,p_{j-1}& r\,p_{j-1}\end{pmatrix},\qquad p_{j-1}=\mathbb P\{Y_{j-1}=1\},$$
--   then for every $2\le i\le n$ the vector $(Y_1,\dots,Y_{i-1})$ has the same joint law as $(X^i_1,\dots,X^i_{i-1})$.
--
--   A single Markov chain thus represents all rows of the graph: the row sum of $v_{i}$ has the law of $S_{i-1}=Y_1+\dots+Y_{i-1}$, which is how the degree analysis reduces to Corollary 4.6.
--
--   Differences from the source:
--   - generalization: the two chains are "equivalent": (a) same initial distribution and (b) same transition matrices (p. 8) → equality of the joint laws: P{(X_1, …, X_{i−1}) = x} agree for every pattern x; reason: for Markov chains, equal joint laws give equal initial laws and transition matrices; it is also the form the proof of Theorem 2.2 uses ("S_i has the same distribution as S^{i+1}_i", p. 12)
--   - reading: Definition 1, p. 3: edge (v_j, v_i) depends on edge (v_{j−1}, v_i) and "is independent of all other edges"; P(present | previous absent) = P(previous present), P(present | previous present) = r·P(previous present) → the law rmrgWeight: the rows (X^i_1, …, X^i_{i−1}), i = 2, …, n, are mutually independent, each row is a Markov chain with X^i_1 ~ Bernoulli(p) and the transition matrix (2), p. 8, whose entries use the marginal of the previous edge, i.e. the iterate recSeq (1 − r) p (j − 1) of f_γ; reason: read literally, independence of all other edges contradicts the dependence on the next edge of the same row; the generation process (pp. 2–3), the transition matrix (2) and the proof of Lemma 3.2 ("intra-iteration dependency but inter-iteration independency", p. 9) fix this reading; Lemma 3.1 certifies that the marginals of the weight obey the recursion Definition 1 presupposes
--   - encoding: vertices v_1, …, v_n; edge variable X^i_j for edge (v_j, v_i), j < i; probabilities under G^r_{n,p} → vertex set Fin n with v_k = k − 1, X^i_j = G.Adj (j − 1) (i − 1); probabilities are rmrgProb n p r E, the weighted sum of rmrgWeight over all SimpleGraph (Fin n); reason: the same finite probability space (Notation, p. 4); every 1-based index range is shifted by one, no instance changes
--   - encoding: a finite Markov chain {X_1, …, X_n} of Bernoulli variables with P{X_1 = 1} = p and transition matrix (2) → an ℕ-indexed chain Y with IsDecayChain P Y (1 − r) and P{Y 0 = 1} = p, on a probability space Ω : Type; its first i − 1 terms; reason: IsDecayChain with β = 1 − r is the printed transition matrix in multiplicative form; the conclusion depends only on the joint law, and every finite such chain is the initial segment, in law, of an infinite one
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, pp. 8–9, Lemma 3.2; "equivalent" defined on p. 8

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory

theorem lemma_3_2 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) :
    (∀ (n : ℕ) (i j : Fin n), 1 ≤ (i : ℕ) → i < j → ∀ x : ℕ → Prop,
      rmrgProb n p r (fun G => ∀ k (hk : k < (i : ℕ)), (G.Adj ⟨k, by omega⟩ j ↔ x k)) =
        rmrgProb n p r (fun G => ∀ k (hk : k < (i : ℕ)), (G.Adj ⟨k, by omega⟩ i ↔ x k))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y : ℕ → Ω → ℝ), IsDecayChain P Y (1 - r) → P.real {ω | Y 0 ω = 1} = p →
      ∀ (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) (x : ℕ → Prop),
        P.real {ω | ∀ k < i - 1, (Y k ω = 1 ↔ x k)} =
          rmrgProb n p r
            (fun G => ∀ k (hk : k < i - 1), (G.Adj ⟨k, by omega⟩ ⟨i - 1, by omega⟩ ↔ x k))) := by sorry

end RecMarkovGraph.IndepLB
