-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_lemma_6_2
-- name    : SpectralSparsify.Sampling.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:12.470288+00:00
-- url     : https://prove2.me/theorems/55500919-c990-4410-9c3a-36c686ba9645
-- title:
--   Lemma 6.2 — if λ₂(D^{-1/2}LD^{-1/2}) ≥ λ and ‖D^{-1/2}(L − L̃)D^{-1/2}‖ ≤ ε, then G̃ is a λ/(λ − ε)-approximation of G
-- statement:
--   Let $G$ be a connected unweighted graph on a vertex set $V$ with $|V|\ge 2$, with Laplacian $L$ and diagonal degree matrix $D$, and let $\widetilde G$ be any weighted graph on $V$ with Laplacian $\widetilde L$. Let $0\le\epsilon<\lambda$. Suppose that
--
--   1. every non-zero eigenvalue of $D^{-1/2}LD^{-1/2}$ is at least $\lambda$ (for connected $G$, $0$ is a simple eigenvalue, so this says $\lambda_2(D^{-1/2}LD^{-1/2})\ge\lambda$), and
--   2. $\big\|D^{-1/2}(L-\widetilde L)D^{-1/2}\big\|\le\epsilon$.
--
--   Then $\widetilde G$ is a $\sigma$-approximation of $G$ for
--   $$\sigma=\frac{\lambda}{\lambda-\epsilon}.$$
--
--   The lemma turns a spectral-norm bound on the normalized difference of Laplacians into a spectral approximation; it is the last step of the proof of Theorem 6.1.
--
--   **Formalization Note** The paper leaves implicit $0\le\epsilon<\lambda$; for $\epsilon\ge\lambda$ the value $\lambda/(\lambda-\epsilon)$ is negative or undefined and the conclusion fails. The norm is the 2-norm of the symmetric matrix $D^{-1/2}(L-\widetilde L)D^{-1/2}$ (all eigenvalues of absolute value at most $\epsilon$). $L$ is Mathlib's `G.lapMatrix ℝ` and $\widetilde L$ is `lapMat wt`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 8, Lemma 6.2

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_SpectralSparsify_Sampling_SpectralNotions

namespace SpectralSparsify.Sampling

/-- Lemma 6.2 (Spielman–Teng, arXiv:0808.4134v3, p. 8). Let `G` be a connected unweighted graph
with at least two vertices, `L` its Laplacian, `D` its degree matrix, and `G̃` (weights `wt`) any
weighted graph on the same vertices with Laplacian `L̃`. If every nonzero eigenvalue of
`D^{-1/2} L D^{-1/2}` is at least `λ` (for connected `G` this is `λ₂ ≥ λ`) and
`‖D^{-1/2}(L - L̃)D^{-1/2}‖ ≤ ε`, then `G̃` is a `λ/(λ - ε)`-approximation of `G`.
The hypothesis `0 ≤ ε < λ` is implicit in the paper. -/
theorem lemma_6_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hV : 2 ≤ Fintype.card V)
    (wt : V → V → ℝ) (hwt : IsWGraph wt) (lam ε : ℝ) (hε : 0 ≤ ε) (hεlam : ε < lam)
    (h1 : NonzeroEigGE (normLap G) lam)
    (h2 : NormLE (normalize G (G.lapMatrix ℝ - lapMat wt)) ε) :
    IsApprox (lam / (lam - ε)) wt (adjWeight G) := by sorry

end SpectralSparsify.Sampling
