-- Prove2me | Theorems.Thm_WeightedEdgeColor_theorem_3_1
-- name    : WeightedEdgeColor.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:49:51.327302+00:00
-- url     : https://prove2.me/theorems/7c0758aa-cf39-4078-9493-05e30a7a3910
-- title:
--   Theorem 3.1 — local-to-global rounding: a feasible partial coloring losing $\varepsilon n+O(n^{3/4})$ weight per vertex
-- statement:
--   Fix constants $C_0,C_1,\varepsilon>0$. Let $G=(V,E)$ be a finite simple graph with edge weights in $(0,1]$ and let $n$ be a real parameter with $W_G(v)\le n$ for every vertex. Let $\mathcal C$ be a palette of at most $C_1n$ colors, and let $x_{e,c}$ ($e\in E$, $c\in\mathcal C$) satisfy, for every edge $e$, color $c$ and vertex $v$,
--   $$
--   0\le x_{e,c}\le\frac{C_0}{n},\qquad \sum_{c\in\mathcal C}x_{e,c}\le1,\qquad (x_{e,c}:e\ni v)\in\mathcal K_v .
--   $$
--   Then there are a threshold $n_0$ and a constant $K$, depending only on $C_0,C_1,\varepsilon$ (not on the number of vertices or the edge weights), such that for $n\ge n_0$ there is a feasible partial coloring of $G$ with colors from $\mathcal C$ that
--   1. uses only pairs $(e,c)$ with $x_{e,c}>0$, and
--   2. has, at every vertex $v$, colored incident weight at least
--   $$
--   \sum_{e\ni v}w_e\sum_{c\in\mathcal C}x_{e,c}-\varepsilon n-K n^{3/4}.
--   $$
--
--   The theorem turns locally feasible fractional color proposals into one globally consistent partial coloring that keeps almost all proposed weight at every vertex; the support condition is what lets the paper reuse it when some colors are unavailable to some edges.
--
--   **Formalization Note** The threshold and the constant are chosen before the graph, the palette, $n$ and $x$. A partial coloring is a map from edges to optional colors.
--
--   Differences from the source:
--   - encoding: "for all sufficiently large $n$" and $O_{C_0,C_1,\varepsilon}(n^{3/4})$ → a threshold $n_0$ and a constant $K$ chosen from $C_0,C_1,\varepsilon$ before the graph; reason: this is the stated independence from the number of vertices and the minimum edge weight
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem 3.1, p.6; restated p.35, proof pp.35–43

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Theorem 3.1 (Local-to-global rounding).

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem 3.1, p.6; restated p.35, proof pp.35–43.

**Formalization Note.** `n` is a real parameter. "For all sufficiently large `n`" is a
threshold `n₀`, and `O_{C₀,C₁,ε}(n^{3/4})` is `Kc · n^{3/4}`; both are chosen from `C₀, C₁, ε`
only, before the vertex and edge types, the graph, the palette and `x`, hence independent of
the number of vertices and of the minimum edge weight. The palette `𝒞` is a finite type with
`|𝒞| ≤ C₁ n`. The partial coloring is `φ : E → Option 𝒞`; "using only pairs with
`x_{e,c} > 0`" is `φ e = some c → 0 < x e c`. -/
theorem theorem_3_1 (C₀ C₁ ε : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hε : 0 < ε) :
    ∃ n₀ Kc : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ x : E → 𝒞 → ℝ, (∀ e c, 0 ≤ x e c ∧ x e c ≤ C₀ / n) → (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.InK v (fun e => x e c)) →
      ∃ φ : E → Option 𝒞, G.IsFeasiblePartialColoring φ ∧
        (∀ e c, φ e = some c → 0 < x e c) ∧
        ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, x e c) - ε * n - Kc * n ^ (3 / 4 : ℝ) ≤
          G.coloredWeight φ v := by sorry

end WeightedEdgeColor
