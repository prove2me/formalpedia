-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_eq_20
-- name    : SpectralSparsify.Pullback.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:34.471518+00:00
-- url     : https://prove2.me/theorems/f395630a-5f62-4eba-ade7-ba27c9f08d53
-- title:
--   (20) — an edge (a, b) between parts is dominated by (1 + 1/c)(f + G₁/(cn²)), f the unit edge between representatives
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph on $n=|V|$ vertices, $\pi:V\to\{1,\dots,k\}$ the map of a partition $V_1,\dots,V_k$, and $G_1$ the graph of the edges of $G$ inside the parts. Let $c\ge 3$ and assume
--
--   1. each set $V_i$ is connected by edges of $G_1$, and
--   2. every edge of $G_1$ has weight at least $c^2n^3$.
--
--   Choose a representative $v_i\in V_i$ for each $i$. Then for any two vertices $a,b$ in different parts, writing $(a,b)$ for the edge of weight $1$ between $a$ and $b$ and $f$ for the edge of weight $1$ between $v_{\pi(a)}$ and $v_{\pi(b)}$,
--   $$(a,b)\preccurlyeq\Big(1+\frac1c\Big)\Big(f+\frac1{cn^2}G_1\Big).$$
--
--   This is display (20) in the proof of claim (a) of Lemma 10.2: an edge between two parts can be routed through the heavy intra-part edges to the representatives at a cost of only a factor $1+1/c$.
--
--   **Formalization Note** The representatives are any \`r : Fin k → V\` with \`π (r i) = i\`; $G_1$ is \`intraPart w π\`, and hypothesis 1 is reachability in \`intraGraph w π\` between any two vertices of the same part. In the paper (20) is stated for edges $(a,b)\in E_0$; the Lean states it for every pair $a,b$ in different parts, which includes them (the left side does not involve $w$). Hypothesis 3 of Lemma 10.2 is not needed here.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 37, proof of Lemma 10.2, claim (a), display (20)

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- (20), proof of Lemma 10.2, claim (a) (arXiv:0808.4134v3, p. 37). Under hypotheses 1 and 2 of
Lemma 10.2 and `c ≥ 3`, for representatives `r i ∈ Vᵢ` and any `a, b` in different parts,
`(a, b) ≼ (1 + 1/c) (f + (1/(c n²)) G₁)`, where `f` is the weight-`1` edge between `r (π a)` and
`r (π b)` and `n = |V|`. -/
theorem eq_20 {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (c : ℝ) (hc : 3 ≤ c)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (r : Fin k → V) (hr : ∀ i, π (r i) = i) (a b : V) (hab : π a ≠ π b) :
    GraphLE (unitEdge a b)
      ((1 + 1 / c) • (unitEdge (r (π a)) (r (π b)) +
        (1 / (c * (Fintype.card V : ℝ) ^ 2)) • intraPart w π)) := by sorry

end SpectralSparsify.Pullback
