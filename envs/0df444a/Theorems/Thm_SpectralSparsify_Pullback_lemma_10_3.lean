-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_lemma_10_3
-- name    : SpectralSparsify.Pullback.lemma_10_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:52.773986+00:00
-- url     : https://prove2.me/theorems/791db18f-3d89-4118-b87f-779a2fc56e3f
-- title:
--   Lemma 10.3 — an edge of weight 1 is dominated by (1/w₁ + ⋯ + 1/w_k) times a path with edge weights w₁, …, w_k
-- statement:
--   Let $u,v$ be vertices and let $(u,v)$ denote the graph consisting of the single edge $\{u,v\}$ of weight $1$. Let $F$ be a path $u=p_0,p_1,\dots,p_k=v$ through distinct vertices, $k\ge 1$, whose edges $\{p_{i-1},p_i\}$ have weights $w_1,\dots,w_k>0$. Then
--   $$(u,v)\preccurlyeq\Big(\frac1{w_1}+\cdots+\frac1{w_k}\Big)F ,$$
--   that is, for every $x\in\mathbb R^V$,
--   $$(x(u)-x(v))^2\le\Big(\sum_{i=1}^k\frac1{w_i}\Big)\sum_{i=1}^k w_i\,(x(p_i)-x(p_{i-1}))^2 .$$
--
--   This is a Poincaré-type path inequality: it bounds how well a path of edges preconditions a single edge joining its endpoints, and it is the tool behind (20) and (21) in the proof of Lemma 10.2.
--
--   **Formalization Note** The path is an injective \`p : Fin (k+1) → V\` with \`p 0 = u\` and \`p (Fin.last k) = v\`, and its weights are \`wt : Fin k → ℝ\`. The paper leaves implicit that the weights are positive (they are edge weights, and $1/w_i$ must make sense) and that $u\neq v$, i.e. $k\ge 1$; both are hypotheses here. The conclusion is \`GraphLE (unitEdge u v) ((∑ i, 1 / wt i) • pathGraph p wt)\`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 37, Lemma 10.3

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_PathGraph

namespace SpectralSparsify.Pullback

/-- Lemma 10.3 (arXiv:0808.4134v3, p. 37). Let `(u, v)` be an edge of weight `1` and let `F` be a
path `u = p 0, p 1, …, p k = v` whose edges have weights `w₁, …, w_k > 0`. Then
`(u, v) ≼ (1/w₁ + ⋯ + 1/w_k) F`. -/
theorem lemma_10_3 {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    (p : Fin (k + 1) → V) (hp : Function.Injective p) (wt : Fin k → ℝ) (hwt : ∀ i, 0 < wt i)
    (u v : V) (hu : p 0 = u) (hv : p (Fin.last k) = v) :
    GraphLE (unitEdge u v) ((∑ i, 1 / wt i) • pathGraph p wt) := by sorry

end SpectralSparsify.Pullback
