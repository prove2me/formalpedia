-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_lemma_10_2
-- name    : SpectralSparsify.Pullback.lemma_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:48.336922+00:00
-- url     : https://prove2.me/theorems/8f2cbbfc-3478-4498-8149-2c7afdf31474
-- title:
--   Lemma 10.2 (Pullback) — G̃₀ + G₁ is a (1 + ε)(1 + 1/c)²-approximation of G
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph on $n=|V|$ vertices, let $V_1,\dots,V_k$ be a partition of $V$ into nonempty parts, and let $\pi$ be its map. Set $E_0=\partial(V_1,\dots,V_k)$, the edges between different parts, $G_0=(V,E_0,w)$, $E_1=E-E_0$ and $G_1=(V,E_1,w)$. Let $0\le\epsilon<1/2$, let $\widetilde H$ be a $(1+\epsilon)$-approximation of the contraction of $G_0$ under $\pi$, and let $\widetilde G_0$ be a pullback of $\widetilde H$ under $\pi$. Let $c\ge 3$ and assume
--
--   1. each set of vertices $V_i$ is connected by edges in $E_1$,
--   2. every edge in $E_1$ has weight at least $c^2n^3$, and
--   3. every edge in $E_0$ has weight $1$.
--
--   Then $\widetilde G_0+G_1$ is an $\alpha$-approximation of $G$ for
--   $$\alpha=(1+\epsilon)\Big(1+\frac1c\Big)^2 .$$
--
--   The lemma says that, when the parts are held together by much heavier edges, a sparsifier of the light edges between them can be built on the contracted graph, with one vertex per part, and pulled back to $V$. It is how Spielman and Teng pass from graphs with bounded weight ratio to arbitrarily weighted graphs (algorithm Sparsify, §10.2).
--
--   **Formalization Note** The partition map is a surjective \`π : V → Fin k\`. $\widetilde H$ is a weighted graph \`zt\` on \`Fin k\` with \`IsApprox (1 + ε) zt (contraction (crossPart w π) π)\`; $\widetilde G_0$ is a weighted graph \`wt\` with \`IsPullback wt zt π\`. Two hypotheses the paper leaves implicit are explicit here, and each is needed for the statement to hold: $\epsilon\ge 0$ ("for some $\epsilon<1/2$"; with $\epsilon<0$ an empty $E_0$ already gives a counterexample, as $\alpha<1$ is possible), and that every edge of the pullback joins two different parts (part of \`IsPullback\`; contraction cannot see an edge inside a part). Hypothesis 1 is reachability in the graph of $E_1$-edges between any two vertices of the same part. The conclusion is \`IsApprox ((1 + ε) * (1 + 1/c)^2) (wt + intraPart w π) w\`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, pp. 36–37, Lemma 10.2 (Pullback)

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- Lemma 10.2 (Pullback), arXiv:0808.4134v3, pp. 36–37. Let `G = (V, E, w)` be a weighted graph,
`V₁, …, V_k` a partition of `V` with map `π`, `G₀` the edges between parts and `G₁` the edges inside
parts. Let `0 ≤ ε < 1/2`, let `H̃` be a `(1 + ε)`-approximation of the contraction of `G₀` under `π`,
and let `G̃₀` be a pullback of `H̃` under `π`. Assume `c ≥ 3` and
1. each `Vᵢ` is connected by edges in `E₁`,
2. every edge in `E₁` has weight at least `c² n³` (`n = |V|`), and
3. every edge in `E₀` has weight `1`.
Then `G̃₀ + G₁` is an `α`-approximation of `G` for `α = (1 + ε)(1 + 1/c)²`. -/
theorem lemma_10_2 {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (hπ : Function.Surjective π)
    (ε c : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hc : 3 ≤ c)
    (zt : Fin k → Fin k → ℝ) (hzt : SpectralSparsify.Sampling.IsWGraph zt)
    (happrox : SpectralSparsify.Sampling.IsApprox (1 + ε) zt (contraction (crossPart w π) π))
    (wt : V → V → ℝ) (hwt : SpectralSparsify.Sampling.IsWGraph wt) (hpb : IsPullback wt zt π)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1) :
    SpectralSparsify.Sampling.IsApprox ((1 + ε) * (1 + 1 / c) ^ 2) (wt + intraPart w π) w := by sorry

end SpectralSparsify.Pullback
