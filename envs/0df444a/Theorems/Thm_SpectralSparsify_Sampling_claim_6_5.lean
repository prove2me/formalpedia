-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_claim_6_5
-- name    : SpectralSparsify.Sampling.claim_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:54.244914+00:00
-- url     : https://prove2.me/theorems/ae42d762-8690-406e-b4d4-ea5a455866d9
-- title:
--   Claim 6.5 — every entry of Δ = D^{-1}(Ã − A) has |Δ_{i,j}| ≤ 1/Υ
-- statement:
--   Let $G$ be an unweighted graph with degrees $d_i\ge 1$, adjacency matrix $A$ and degree matrix $D$. Sample its edges with the probabilities $p_{i,j}=\min(1,\Upsilon/\min(d_i,d_j))$ of (4) for a parameter $\Upsilon>1$, giving the adjacency matrix $\widetilde A$ of the sampled graph, and let $\Delta=D^{-1}(\widetilde A-A)$. Then for every outcome of the sampling that has positive probability, and all $i,j$,
--   $$|\Delta_{i,j}|\le\frac1\Upsilon,$$
--   that is, the bound holds with probability one.
--
--   The claim is the uniform entry bound used to control the higher moments of $\Delta$ (Lemma 6.6).
--
--   **Formalization Note** The paper states the claim for the entries of $\Delta$ on edges; on non-edges and on the diagonal $\Delta_{i,j}=0$, so the Lean statement quantifies over all $i,j$. An outcome is a set $T$ of edges of $G$ with positive probability $\prod_{e\in T}p_e\prod_{e\in E\setminus T}(1-p_e)>0$; this excludes exactly the outcomes that drop an edge with $p_{i,j}=1$, on which $\Delta_{i,j}=-1/d_i$ can exceed $1/\Upsilon$ (the paper's "if $p_{i,j}=1$, then $\Delta_{i,j}=0$" is an almost-sure statement). The paper leaves implicit that every degree is positive ($D^{-1}$ requires it); the standing assumption $\Upsilon>1$ comes with (4).
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 13, Claim 6.5 (Δ defined on p. 10)

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

namespace SpectralSparsify.Sampling

/-- Claim 6.5 (Spielman–Teng, arXiv:0808.4134v3, p. 13). Let `G` be an unweighted graph with no
isolated vertex, sample its edges with the probabilities (4) for a parameter `Υ > 1`, and let
`Δ = D^{-1}(Ã - A)`. For every outcome `T ⊆ E` of positive probability and all `i, j`,
`|Δ_{i,j}| ≤ 1/Υ` (the bound holds with probability one: an edge with `p_{i,j} = 1` is always
kept, and the outcomes that drop it have probability `0`). -/
theorem claim_6_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (Υ : ℝ) (hΥ : 1 < Υ)
    (T : Finset (Sym2 V)) (hT : T ⊆ G.edgeFinset)
    (hTpos : 0 < outcomeProb G.edgeFinset (degSampleProb G Υ) T) (i j : V) :
    |deltaMat G (degSampleProb G Υ) T i j| ≤ 1 / Υ := by sorry

end SpectralSparsify.Sampling
