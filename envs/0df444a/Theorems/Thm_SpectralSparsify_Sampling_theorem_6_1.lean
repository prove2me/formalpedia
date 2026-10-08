-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_theorem_6_1
-- name    : SpectralSparsify.Sampling.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:33:11.462985+00:00
-- url     : https://prove2.me/theorems/6f1f89b8-b753-437f-9199-61bb7c569f4a
-- title:
--   Theorem 6.1 (Sampling High-Conductance Graphs) — with probability ≥ 1 − p, G̃ = (V, F̃ ∪ H) is a (1+ε)-approximation of G and |F̃| ≤ 288k²/(ελ)²·|S|
-- statement:
--   Let $\epsilon,p\in(0,1/2)$ and let $G=(V,E)$ be an unweighted graph without isolated vertices whose smallest non-zero normalized Laplacian eigenvalue is at least $\lambda>0$. Let $S\subseteq V$, let $F$ be the edges of the induced subgraph $G(S)$ and $H=E-F$ the rest of the edges. Let $k$ be an even integer with
--   $$k\ge\log_2(3/p)\quad\text{and}\quad k\ge\log_2|S|,$$
--   and let $(S,\widetilde F)=\mathtt{Sample}((S,F),\epsilon,p,\lambda)$ with this $k$: with $\Upsilon=(12k/(\epsilon\lambda))^2$ and $d_i$ the degree of $i$ in $G(S)$, each edge $(i,j)\in F$ is kept independently with probability $p_{i,j}=\min(1,\Upsilon/\min(d_i,d_j))$ and then has weight $1/p_{i,j}$. Let $\widetilde G=(V,\widetilde F\cup H)$, the edges of $H$ keeping weight $1$. Then, with probability at least $1-p$, both
--
--   1. (S.1) $\widetilde G$ is a $(1+\epsilon)$-approximation of $G$, and
--   2. (S.2) the number of edges in $\widetilde F$ is at most
--   $$\frac{288\,k^2}{(\epsilon\lambda)^2}\,|S|.$$
--
--   This is the sampling theorem of the paper: in a graph of high conductance (large $\lambda$), keeping each edge with probability inversely proportional to the smaller endpoint degree yields a spectral approximation with $O(|S|\log^2(\cdot)/(\epsilon\lambda)^2)$ edges. It is the step that the paper combines with graph decompositions to sparsify arbitrary graphs.
--
--   **Formalization Note** The paper sets $k=\max(\log_2(3/p),\log_2 n)$ in $\mathtt{Sample}$, but its proof applies Lemma 6.3, which holds for even integers $k$, with this $k$; for a real $k$ the proof does not go through, and rounding breaks its constants. The statement therefore takes any even natural number $k$ above both logarithms; the printed theorem is the case where the maximum is itself an even integer. $n$ in $\mathtt{Sample}$ is the number of vertices of its input $(S,F)$, i.e. $|S|$. Implicit hypotheses made explicit: every vertex of $G$ has degree at least $1$ ($\mathcal L_G$ requires $D^{-1/2}$) and $\lambda>0$. $G$ is not assumed connected. The two conclusions hold simultaneously on one event of probability at least $1-p$; probability is over the independent sampling of the edges of $F$ (finite sum over the outcomes $T\subseteq F$, with $\widetilde F=T$).
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 8, Theorem 6.1 and the procedure Sample (proof pp. 15–16)

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_SpectralNotions
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling
import Definitions.Def_SpectralSparsify_Sampling_Sample

namespace SpectralSparsify.Sampling

/-- Theorem 6.1 (Sampling High-Conductance Graphs; Spielman–Teng, arXiv:0808.4134v3, p. 8). Let
`ε, p ∈ (0, 1/2)` and let `G = (V, E)` be an unweighted graph with no isolated vertex whose smallest
nonzero normalized Laplacian eigenvalue is at least `λ > 0`. Let `S ⊆ V`, let `F` be the edges of
`G(S)` and `H = E - F`. Run `Sample((S, F), ε, p, λ)` with an even integer `k ≥ log₂(3/p)`,
`k ≥ log₂ |S|`: each edge `{i, j} ∈ F` is kept independently with probability
`p_{i,j} = min(1, Υ / min(d_i, d_j))`, `Υ = (12k/(ελ))²`, `d_i` the degree in `G(S)`, and gets weight
`1/p_{i,j}`; `G̃ = (V, F̃ ∪ H)` with weight `1` on `H`. Then with probability at least `1 - p`,
(S.1) `G̃` is a `(1+ε)`-approximation of `G`, and (S.2) `|F̃| ≤ 288 k² / (ελ)² · |S|`.
The paper sets `k = max(log₂(3/p), log₂ n)`; its proof needs `k` to be an even integer, so `k` is a
parameter here (the printed statement is the case where that maximum is an even integer). -/
theorem theorem_6_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (ε p lam : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (hlam : 0 < lam) (hspec : NonzeroEigGE (normLap G) lam)
    (S : Finset V) (k : ℕ) (hk : Even k)
    (hk1 : Real.logb 2 (3 / p) ≤ k) (hk2 : Real.logb 2 S.card ≤ k) :
    1 - p ≤ prob (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T =>
        IsApprox (1 + ε) (sparsifierWeight G S (sampleSubgraphProb G S k ε lam) T)
            (adjWeight G) ∧
          (T.card : ℝ) ≤ 288 * (k : ℝ) ^ 2 / (ε * lam) ^ 2 * S.card) := by sorry

end SpectralSparsify.Sampling
