-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_eq_21
-- name    : SpectralSparsify.Pullback.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:11.751789+00:00
-- url     : https://prove2.me/theorems/92160faa-4009-4e73-8ea7-ddaf33b3d744
-- title:
--   (21) — the unit edge f between representatives is dominated by (1 + 1/c)((a, b) + G₁/(cn²))
-- statement:
--   In the setting of (20): $G=(V,E,w)$ a weighted graph on $n=|V|$ vertices, $\pi$ the map of a partition $V_1,\dots,V_k$, $G_1$ the graph of the edges inside the parts, $c\ge 3$, each $V_i$ connected by edges of $G_1$, and every edge of $G_1$ of weight at least $c^2n^3$. Choose representatives $v_i\in V_i$. For any $a,b$ in different parts, with $(a,b)$ the unit edge between $a$ and $b$ and $f$ the unit edge between $v_{\pi(a)}$ and $v_{\pi(b)}$,
--   $$f\preccurlyeq\Big(1+\frac1c\Big)\Big((a,b)+\frac1{cn^2}G_1\Big).$$
--
--   This is display (21), the reverse of (20); summing it over $E_0$ gives the second half of claim (a) of Lemma 10.2.
--
--   **Formalization Note** Same conventions as (20): representatives \`r\` with \`π (r i) = i\`, $G_1$ = \`intraPart w π\`, hypothesis 1 as reachability in \`intraGraph w π\`; stated for all pairs $a,b$ in different parts.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 38, proof of Lemma 10.2, claim (a), display (21)

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- (21), proof of Lemma 10.2, claim (a) (arXiv:0808.4134v3, p. 38). Under hypotheses 1 and 2 of
Lemma 10.2 and `c ≥ 3`, for representatives `r i ∈ Vᵢ` and any `a, b` in different parts,
`f ≼ (1 + 1/c) ((a, b) + (1/(c n²)) G₁)`, where `f` is the weight-`1` edge between `r (π a)` and
`r (π b)` and `n = |V|`. -/
theorem eq_21 {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (c : ℝ) (hc : 3 ≤ c)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (r : Fin k → V) (hr : ∀ i, π (r i) = i) (a b : V) (hab : π a ≠ π b) :
    GraphLE (unitEdge (r (π a)) (r (π b)))
      ((1 + 1 / c) • (unitEdge a b +
        (1 / (c * (Fintype.card V : ℝ) ^ 2)) • intraPart w π)) := by sorry

end SpectralSparsify.Pullback
