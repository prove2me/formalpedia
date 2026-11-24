-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_grouping
-- name    : WeightedEdgeColor.lemma_grouping
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T05:47:15.095793+00:00
-- url     : https://prove2.me/theorems/22052f99-e59a-48c7-a4aa-83896932cc04
-- title:
--   Grouping step: $L_{v,j}\le W_G(v)/r+O(\sqrt{n\log n})$
-- statement:
--   This is the grouping step in the proof of Theorem 3.1 (local-to-global rounding).
--
--   Let $r\ge 1$ be an integer. There is a constant $K$, depending only on $r$, with the following property. Let $G=(V,E)$ be a finite simple graph with edge weights $w:E\to(0,1]$, and let $n\ge 2$ be a real number such that every weighted degree satisfies $W_G(v)=\sum_{e\ni v}w_e\le n$. Then the vertices can be divided into $r$ groups $V_1,\dots,V_r$ such that, for every vertex $v$ and every group $j$, the weight from $v$ to group $j$ satisfies
--
--   $$
--   L_{v,j}=\sum_{u:\ uv\in E(G),\ u\in V_j} w_{uv}\;\le\;\frac{W_G(v)}{r}+K\sqrt{n\log n}.
--   $$
--
--   The bound does not depend on the number of vertices or on the minimum edge weight, so arbitrarily many edges of very small weight are allowed. In the proof of Theorem 3.1 it shows that the edges inside the groups have total weight at most $n/r+O(\sqrt{n\log n})$ at every vertex. Those edges are set aside, and the remaining graph has no edges inside a group.
--
--   In the source the bound follows from Proposition A.4 (Harris–Srinivasan). The independent choices are the groups of the vertices, and the sums are the $L_{v,j}$. Simplicity makes every single contribution $w_{uv}\le1$. A choice at $u$ contributes $W_G(u)\le n$ in total over all sums. This gives $R\le n/r$ and $D\le n$.
--
--   **Formalization Note.** The groups are a map $g:V\to\{0,\dots,r-1\}$ (`Fin r`). An edge $e$ at $v$ counts toward $L_{v,j}$ when some endpoint $u\ne v$ of $e$ has $g(u)=j$; since edges are loopless, this is the other endpoint. The real parameter $n\ge2$ makes $\log n>0$. The constant $K$ is chosen before the graph.
-- source:
--   R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190 (preprint of November 2, 2026), proof of Theorem 3.1, paragraph 'Dividing the vertices into groups', pp.35-36 (uses Proposition A.4, p.26)

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false
namespace WeightedEdgeColor

theorem lemma_grouping (r : ℕ) (hr : 0 < r) :
    ∃ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ n : ℝ, 2 ≤ n → (∀ v, G.W v ≤ n) →
      ∃ g : V → Fin r, ∀ (v : V) (j : Fin r),
        ∑ e ∈ (G.inc v).filter (fun e => ∃ u, u ≠ v ∧ u ∈ G.ends e ∧ g u = j), G.w e
          ≤ G.W v / r + K * Real.sqrt (n * Real.log n) := by sorry

end WeightedEdgeColor
