-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_lemma_6_3
-- name    : SpectralSparsify.Sampling.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:19.206178+00:00
-- url     : https://prove2.me/theorems/3de74207-9c7c-4cb7-9985-e60e731080c4
-- title:
--   Lemma 6.3 (Random Subgraph) — Pr[‖D^{-1/2}(Ã − A)D^{-1/2}‖ ≥ 2kn^{1/k}/√Υ] ≤ 2^{-k} for even k
-- statement:
--   Let $G$ be an unweighted graph on $n$ vertices with degrees $d_i\ge1$, adjacency matrix $A$ and degree matrix $D$, and let $\widetilde A$ be the adjacency matrix of the graph obtained by sampling each edge independently with the probability (4), $p_{i,j}=\min(1,\Upsilon/\min(d_i,d_j))$, $\Upsilon>1$, and weighting a kept edge by $1/p_{i,j}$. For every positive even integer $k$,
--   $$\Pr\Big[\big\|D^{-1/2}(\widetilde A-A)D^{-1/2}\big\|\ge\frac{2k\,n^{1/k}}{\sqrt\Upsilon}\Big]\le 2^{-k}.$$
--
--   The lemma bounds the first of the two terms into which the proof of Theorem 6.1 splits $\|D^{-1/2}(L-\widetilde L)D^{-1/2}\|$.
--
--   **Formalization Note** "$\|M\|\ge t$" for the symmetric matrix $M=D^{-1/2}(\widetilde A-A)D^{-1/2}$ is "some eigenvalue $\mu$ of $M$ has $|\mu|\ge t$". The paper says "for all even integers $k$"; $k\le0$ is excluded ($n^{1/k}$ and $2^{-k}$ lose their meaning), so $k$ is a positive even natural number. $n^{1/k}$ is the real power. The paper leaves implicit that every degree is positive.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 9, Lemma 6.3

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_SpectralNotions
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

namespace SpectralSparsify.Sampling

/-- Lemma 6.3 (Random Subgraph; Spielman–Teng, arXiv:0808.4134v3, p. 9). Let `G` be an unweighted
graph on `n` vertices with no isolated vertex, adjacency matrix `A` and degree matrix `D`, whose
edges are sampled independently with the probabilities (4) for a parameter `Υ > 1`; `Ã` is the
adjacency matrix of the sampled graph. For every positive even integer `k`,
`Pr[‖D^{-1/2}(Ã - A)D^{-1/2}‖ ≥ 2 k n^{1/k} / √Υ] ≤ 2^{-k}`. -/
theorem lemma_6_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (Υ : ℝ) (hΥ : 1 < Υ)
    (k : ℕ) (hk : Even k) (hk0 : 0 < k) :
    prob G.edgeFinset (degSampleProb G Υ)
        (fun T => NormGE
          (normalize G (adjMat (sampledWeight (degSampleProb G Υ) T) - G.adjMatrix ℝ))
          (2 * k * (Fintype.card V : ℝ) ^ ((1 : ℝ) / k) / Real.sqrt Υ)) ≤
      1 / 2 ^ k := by sorry

end SpectralSparsify.Sampling
