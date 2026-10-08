-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_lemma_6_6
-- name    : SpectralSparsify.Sampling.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:01.90999+00:00
-- url     : https://prove2.me/theorems/dce2cce9-54ae-475b-b891-86c28602e0e4
-- title:
--   Lemma 6.6 — for every edge (r, t), k ≥ 1, l ≥ 0: E[Δ_{r,t}^k Δ_{t,r}^l] ≤ (1/Υ^{k+l−1})(1/d_r)
-- statement:
--   Let $G$ be an unweighted graph with degrees $d_i\ge 1$, whose edges are sampled independently with the probabilities (4), $p_{i,j}=\min(1,\Upsilon/\min(d_i,d_j))$, for a parameter $\Upsilon>1$, and let $\Delta=D^{-1}(\widetilde A-A)$. For every edge $(r,t)$ of $G$ and all integers $k\ge 1$, $l\ge 0$,
--   $$\mathbf E\big[\Delta_{r,t}^{\,k}\,\Delta_{t,r}^{\,l}\big]\le\frac{1}{\Upsilon^{k+l-1}}\,\frac1{d_r},$$
--   where $\Delta_{r,t}^{\,k}$ is the $k$-th power of the entry $\Delta_{r,t}$.
--
--   These moment bounds are the input to the trace-method bound of Lemma 6.4.
--
--   **Formalization Note** The paper leaves implicit that every degree is positive. The expectation is over the independent sampling of all edges of $G$ (finite sum over outcomes). $k+l-1$ is a natural number because $k\ge1$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 13, Lemma 6.6

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

namespace SpectralSparsify.Sampling

/-- Lemma 6.6 (Spielman–Teng, arXiv:0808.4134v3, p. 13). Let `G` be an unweighted graph with no
isolated vertex whose edges are sampled independently with the probabilities (4) for a parameter
`Υ > 1`, and let `Δ = D^{-1}(Ã - A)`. For every edge `(r, t)` and integers `k ≥ 1`, `l ≥ 0`,
`E[Δ_{r,t}^k Δ_{t,r}^l] ≤ (1/Υ^{k+l-1}) (1/d_r)` (powers of the entries). -/
theorem lemma_6_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (Υ : ℝ) (hΥ : 1 < Υ)
    (r t : V) (hrt : G.Adj r t) (k l : ℕ) (hk : 1 ≤ k) :
    expect G.edgeFinset (degSampleProb G Υ)
        (fun T => deltaMat G (degSampleProb G Υ) T r t ^ k *
          deltaMat G (degSampleProb G Υ) T t r ^ l) ≤
      1 / Υ ^ (k + l - 1) * (1 / (G.degree r : ℝ)) := by sorry

end SpectralSparsify.Sampling
