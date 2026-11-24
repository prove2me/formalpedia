-- Prove2me | Theorems.Thm_WeightedEdgeColor_theorem_3_1_partite
-- name    : WeightedEdgeColor.theorem_3_1_partite
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T05:47:22.746271+00:00
-- url     : https://prove2.me/theorems/c087991d-d2bf-4fea-942f-b75923cf00f3
-- title:
--   Theorem 3.1 for graphs with no edges inside $r$ groups (rounding on $H$)
-- statement:
--   This is the rounding part of the proof of Theorem 3.1 (local-to-global rounding), stated for graphs whose vertices are divided into a fixed number of groups with no edge inside a group.
--
--   Fix constants $C_0,C_1,\varepsilon>0$ and an integer $r$. Let $G$ be a finite simple graph with edge weights in $(0,1]$, together with a division of its vertices into $r$ groups such that no edge joins two vertices of the same group. Let $n$ be a real parameter with $W_G(v)\le n$ for every vertex, and let $\mathcal C$ be a palette of at most $C_1 n$ colors. Suppose that, for every edge $e$, color $c$ and vertex $v$,
--
--   $$
--   0\le x_{e,c}\le \frac{C_0}{n},\qquad \sum_{c\in\mathcal C}x_{e,c}\le 1,\qquad (x_{e,c}:e\ni v)\in\mathcal K_v ,
--   $$
--
--   where $\mathcal K_v=\operatorname{conv}\{\mathbf 1_S: S\subseteq E(v),\ \sum_{e\in S}w_e\le 1\}$. Then, for all sufficiently large $n$, there is a feasible partial coloring that uses only pairs $(e,c)$ with $x_{e,c}>0$ and whose colored incident weight at every vertex $v$ is at least
--
--   $$
--   \sum_{e\ni v}w_e\sum_{c\in\mathcal C}x_{e,c}\;-\;\varepsilon n\;-\;O_{C_0,C_1,\varepsilon,r}\big(n^{3/4}\big).
--   $$
--
--   The threshold and the hidden constant depend only on $C_0,C_1,\varepsilon,r$, not on the number of vertices or the minimum edge weight.
--
--   In the source this is the graph $H$ in the proof of Theorem 3.1, which remains after the edges inside the groups are set aside (p.36: "Until the final error calculation, work only with $H$"). Together with the grouping step, which divides any simple graph into $r$ groups whose internal edges have weight at most $n/r+O(\sqrt{n\log n})$ at each vertex, it gives Theorem 3.1.
--
--   **Formalization Note.** The groups are a map $g:V\to$ `Fin r` with $g(u)\ne g(v)$ for every edge $uv$. The threshold $n_0$ and the constant $K_c$ of $O(n^{3/4})$ are chosen from $C_0,C_1,\varepsilon,r$ before the graph, palette and proposals. Partial colorings are maps $E\to$ `Option` $\mathcal C$, and membership in $\mathcal K_v$ is the convex-hull condition `InK`. Apart from the group map, the statement is word for word the formal statement of Theorem 3.1.
-- source:
--   R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190 (preprint of November 2, 2026), proof of Theorem 3.1, pp.36-43 (from 'Until the final error calculation, work only with H' to the final error calculation, p.42-43)

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets

set_option autoImplicit false
namespace WeightedEdgeColor

theorem theorem_3_1_partite (C₀ C₁ ε : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hε : 0 < ε) (r : ℕ) :
    ∃ n₀ Kc : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ x : E → 𝒞 → ℝ, (∀ e c, 0 ≤ x e c ∧ x e c ≤ C₀ / n) → (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.InK v (fun e => x e c)) →
      ∃ φ : E → Option 𝒞, G.IsFeasiblePartialColoring φ ∧
        (∀ e c, φ e = some c → 0 < x e c) ∧
        ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, x e c) - ε * n - Kc * n ^ (3 / 4 : ℝ) ≤
          G.coloredWeight φ v := by sorry

end WeightedEdgeColor
