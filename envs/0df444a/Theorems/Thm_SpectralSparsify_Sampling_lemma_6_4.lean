-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_lemma_6_4
-- name    : SpectralSparsify.Sampling.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:00.44593+00:00
-- url     : https://prove2.me/theorems/e832fd29-64a4-473b-b245-6f5b5e21af5b
-- title:
--   Lemma 6.4 — for even k, E[Tr(Δ^k)] ≤ n k^k / Υ^{k/2}
-- statement:
--   Let $G$ be an unweighted graph on $n$ vertices with degrees $d_i\ge1$, whose edges are sampled independently with the probabilities (4) for a parameter $\Upsilon>1$, and let $\Delta=D^{-1}(\widetilde A-A)$. For every even $k$,
--   $$\mathbf E\big[\operatorname{Tr}(\Delta^k)\big]\le\frac{n\,k^k}{\Upsilon^{k/2}},$$
--   where $\Delta^k$ is the $k$-th matrix power.
--
--   This is the trace-method estimate (a refinement of Füredi and Komlós) from which Lemma 6.3 follows by Markov's inequality.
--
--   **Formalization Note** $k$ is a natural number with `Even k` ($k=0$ included, where both sides equal $n$ with $0^0=1$); $k/2$ is exact. The paper leaves implicit that every degree is positive.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 10, Lemma 6.4

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

namespace SpectralSparsify.Sampling

/-- Lemma 6.4 (Spielman–Teng, arXiv:0808.4134v3, p. 10). Let `G` be an unweighted graph on `n`
vertices with no isolated vertex whose edges are sampled independently with the probabilities (4)
for a parameter `Υ > 1`, and let `Δ = D^{-1}(Ã - A)`. For even `k`,
`E[Tr(Δ^k)] ≤ n k^k / Υ^{k/2}` (`Δ^k` the matrix power). -/
theorem lemma_6_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (Υ : ℝ) (hΥ : 1 < Υ)
    (k : ℕ) (hk : Even k) :
    expect G.edgeFinset (degSampleProb G Υ)
        (fun T => ((deltaMat G (degSampleProb G Υ) T) ^ k).trace) ≤
      (Fintype.card V : ℝ) * (k : ℝ) ^ k / Υ ^ (k / 2) := by sorry

end SpectralSparsify.Sampling
