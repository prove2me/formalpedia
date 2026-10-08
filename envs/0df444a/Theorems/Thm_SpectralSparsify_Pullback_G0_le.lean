-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_G0_le
-- name    : SpectralSparsify.Pullback.G0_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:32.018408+00:00
-- url     : https://prove2.me/theorems/c7d1da57-0397-4585-a575-16717e4be9ed
-- title:
--   Summing (20) over E₀ — G₀ ≼ (1 + 1/c)[F + G₁/(2c)]
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph on $n=|V|$ vertices, $\pi$ the map of a partition $V_1,\dots,V_k$, $G_0$ the graph of the edges between different parts and $G_1$ the graph of the edges inside the parts. Let $c\ge 3$ and assume
--
--   1. each $V_i$ is connected by edges of $G_1$,
--   2. every edge of $G_1$ has weight at least $c^2n^3$, and
--   3. every edge of $G_0$ has weight $1$.
--
--   Choose representatives $v_i\in V_i$, let $H$ be the contraction of $G_0$ under $\pi$, and let $F$ be the weighted graph on $\{v_1,\dots,v_k\}$ isomorphic to $H$ under $i\mapsto v_i$. Then
--   $$G_0\preccurlyeq\Big(1+\frac1c\Big)\Big[F+\frac1{2c}G_1\Big].$$
--
--   This is the first half of claim (a) of Lemma 10.2, obtained in the paper by summing (20) over the fewer than $n^2/2$ edges of $E_0$.
--
--   **Formalization Note** $G_0$ is \`crossPart w π\`, $G_1$ is \`intraPart w π\`, and $F$ is \`liftAlong r (contraction (crossPart w π) π)\` for representatives \`r\` with \`π (r i) = i\`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 38, proof of Lemma 10.2, claim (a) (unnumbered display after (21))

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- Summing (20) over `E₀` (proof of Lemma 10.2, claim (a), arXiv:0808.4134v3, p. 38):
`G₀ ≼ (1 + 1/c) [F + (1/(2c)) G₁]`, where `F` is the contraction `H` of `G₀` placed on the
representatives `r i ∈ Vᵢ`. Hypotheses 1–3 of Lemma 10.2 and `c ≥ 3`. -/
theorem G0_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (c : ℝ) (hc : 3 ≤ c)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1)
    (r : Fin k → V) (hr : ∀ i, π (r i) = i) :
    GraphLE (crossPart w π)
      ((1 + 1 / c) • (liftAlong r (contraction (crossPart w π) π) +
        (1 / (2 * c)) • intraPart w π)) := by sorry

end SpectralSparsify.Pullback
