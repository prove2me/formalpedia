-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_lemma_6_7
-- name    : SpectralSparsify.Sampling.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:28.072315+00:00
-- url     : https://prove2.me/theorems/b68c4a02-d24b-49d2-8b9d-a1985a04596d
-- title:
--   Lemma 6.7 — Pr[‖D^{-1/2}(D − D̃)D^{-1/2}‖ ≥ ε] ≤ 2n e^{−Υε²/3} for 0 < ε < 1
-- statement:
--   Let $G$ be an unweighted graph on $n$ vertices with degrees $d_i\ge1$ and degree matrix $D$, and let $\widetilde G$ be obtained by sampling each edge of $G$ independently with the probability (4), $p_{i,j}=\min(1,\Upsilon/\min(d_i,d_j))$, $\Upsilon>1$, a kept edge getting weight $1/p_{i,j}$. Let $\widetilde D$ be the diagonal matrix of weighted degrees of $\widetilde G$. Then for every $0<\epsilon<1$,
--   $$\Pr\Big[\big\|D^{-1/2}(D-\widetilde D)D^{-1/2}\big\|\ge\epsilon\Big]\le 2n\,e^{-\Upsilon\epsilon^2/3}.$$
--
--   The lemma bounds the second of the two terms into which the proof of Theorem 6.1 splits $\|D^{-1/2}(L-\widetilde L)D^{-1/2}\|$.
--
--   **Formalization Note** The paper leaves implicit $0<\epsilon<1$: its proof uses the $\epsilon<1$ form of Theorem 6.8, its only application has $\epsilon=\epsilon\lambda/3<1$, and without an upper bound on $\epsilon$ the printed inequality is false (for $G=K_{d+1}$ with $d\approx1000$, $\Upsilon=3$, $\epsilon=10$ the left side is about $e^{-54}$, the right side about $2000e^{-100}$). It also leaves implicit that every degree is positive. "$\|M\|\ge\epsilon$" means some eigenvalue of the diagonal matrix $M$ has absolute value at least $\epsilon$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 14, Lemma 6.7

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_SpectralNotions
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

namespace SpectralSparsify.Sampling

/-- Lemma 6.7 (Spielman–Teng, arXiv:0808.4134v3, p. 14). Let `G` be an unweighted graph on `n`
vertices with no isolated vertex, and let `G̃` be obtained by sampling the edges of `G`
independently with the probabilities (4) for a parameter `Υ > 1`. Let `D` be the degree matrix of
`G` and `D̃` the diagonal matrix of weighted degrees of `G̃`. For `0 < ε < 1`,
`Pr[‖D^{-1/2}(D - D̃)D^{-1/2}‖ ≥ ε] ≤ 2 n e^{-Υε²/3}`. The range `ε < 1` is not printed; without
it the bound fails for large `ε`. -/
theorem lemma_6_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (Υ : ℝ) (hΥ : 1 < Υ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    prob G.edgeFinset (degSampleProb G Υ)
        (fun T => NormGE
          (normalize G (G.degMatrix ℝ - degMat (sampledWeight (degSampleProb G Υ) T))) ε) ≤
      2 * (Fintype.card V : ℝ) * Real.exp (-(Υ * ε ^ 2) / 3) := by sorry

end SpectralSparsify.Sampling
