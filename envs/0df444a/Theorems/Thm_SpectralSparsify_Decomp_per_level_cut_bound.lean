-- Prove2me | Theorems.Thm_SpectralSparsify_Decomp_per_level_cut_bound
-- name    : SpectralSparsify.Decomp.per_level_cut_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:26.217319+00:00
-- url     : https://prove2.me/theorems/b2adb57d-d333-4d3e-aa05-e1b0af751504
-- title:
--   Proof of Theorem 7.1 — at one level of the recursion at most a φ fraction of the edges is cut
-- statement:
--   Let $G=(V,E)$ be a finite simple graph without isolated vertices, let $\varphi\ge0$, and let $B_1,\dots,B_r\subseteq V$ be pairwise disjoint. Suppose that for every $j$ the set $S_j\subset B_j$ is a proper subset satisfying (C.1) $\operatorname{Vol}(S_j)\le\operatorname{Vol}(B_j)/2$ and (C.2) $\Phi^G_{B_j}(S_j)\le\varphi$. Then
--   $$\sum_{j=1}^{r}|E(S_j,\,B_j-S_j)|\ \le\ \varphi\,|E| .$$
--
--   The sets $B_j$ are the sets split at one level of the recursion of idealDecomp, and $E(S_j,B_j-S_j)$ are the edges that this level adds to the boundary $\partial(A_1,\dots,A_k)$. Together with the depth bound $\log_{4/3}\operatorname{Vol}(V)$ of the recursion this gives $|\partial(A_1,\dots,A_k)|\le|E|\,\varphi\log_{4/3}\operatorname{Vol}(V)$.
--
--   **Formalization Note** The paper's $\varphi=(2\log_{4/3}\operatorname{Vol}(V))^{-1}$ is positive; the statement assumes only $\varphi\ge0$ (for negative $\varphi$ and no sets the right-hand side would be negative). The absence of isolated vertices is the standing hypothesis of the mission. The index set of the family is any finite type.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 19, proof of Theorem 7.1 ("at most a φ fraction of the edges are added to ∂(A1, . . . , Ak) at each level of the recursion")

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol
import Definitions.Def_SpectralSparsify_Decomp_cutEdges
import Definitions.Def_SpectralSparsify_Decomp_cond

namespace SpectralSparsify.Decomp

/-- "At most a `φ` fraction of the edges are added to `∂(A₁, …, A_k)` at each level of the
recursion" (arXiv:0808.4134v3, proof of Theorem 7.1, p. 19): if `B₁, …, B_r` are pairwise
disjoint and each `Sⱼ ⊂ Bⱼ` satisfies (C.1) `Vol(Sⱼ) ≤ Vol(Bⱼ)/2` and (C.2)
`Φ^G_{Bⱼ}(Sⱼ) ≤ φ`, then `∑ⱼ |E(Sⱼ, Bⱼ - Sⱼ)| ≤ φ |E|`. -/
theorem per_level_cut_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (φ : ℝ) (hφ : 0 ≤ φ)
    {ι : Type*} [Fintype ι] (B S : ι → Finset V)
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) (hSB : ∀ j, S j ⊂ B j)
    (hC1 : ∀ j, vol G (S j) ≤ vol G (B j) / 2) (hC2 : ∀ j, condRel G (B j) (S j) ≤ φ) :
    ∑ j, (cutEdges G (S j) (B j \ S j) : ℝ) ≤ φ * (G.edgeFinset.card : ℝ) := by sorry

end SpectralSparsify.Decomp
