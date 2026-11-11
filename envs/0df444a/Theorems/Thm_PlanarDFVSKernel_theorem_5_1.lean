-- Prove2me | Theorems.Thm_PlanarDFVSKernel_theorem_5_1
-- name    : PlanarDFVSKernel.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:35.296961+00:00
-- url     : https://prove2.me/theorems/ec99ce05-af4e-45bd-a579-f7295900ef7c
-- title:
--   Theorem 5.1 — $O((|S|+1)^4)$ traces of incoming balls in a planar digraph
-- statement:
--   **Theorem 5.1** (from Le–Wulff-Nilsen and Sauer–Shelah). In a planar digraph with nonnegative arc lengths, fix a set $S$ of marked vertices. The number of distinct sets $B^-(v,r)\cap S$, over all centres $v$ and radii $r\ge0$, is $O((|S|+1)^4)$. Here $B^-(v,r)=\{u: d(u,v)\le r\}$ is the incoming ball and $d$ the directed shortest-path distance ($\infty$ if unreachable).
--
--   That is, there is an absolute constant $c$ such that for every planar digraph, all nonnegative real lengths and every $S$,
--   $$\bigl|\{B^-(v,r)\cap S : v\in V,\ r\ge0\}\bigr|\le c\,(|S|+1)^4.$$
--
--   Differences from the source:
--   - encoding: O((|S| + 1)⁴) → c·(|S| + 1)⁴ with c chosen before the graph, lengths and S; reason: the O(·) of the statement is uniform over all instances
--   - encoding: nonnegative arc lengths, radii r ≥ 0, d = ∞ if unreachable → lengths and radii in ℝ≥0, distance as an infimum over walks in [0, ∞]; reason: the same distances
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Theorem 5.1 (from [LWN24, Sau72]), p.19 (PDF 20)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_dist

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp
open scoped NNReal ENNReal

open Classical in
/-- **Theorem 5.1** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Theorem 5.1 (from [LWN24, Sau72]), p.19 (PDF 20)): "In a planar digraph
with nonnegative arc lengths, fix a set S of marked vertices. The number of distinct sets
B⁻(v, r) ∩ S, over all centers v and radii r ≥ 0, is O((|S| + 1)⁴)."

There is a constant `c` such that for every planar digraph, all nonnegative real arc lengths `ℓ`
and every vertex set `S`, the number of distinct sets `B⁻(v, r) ∩ S = {u ∈ S : d(u, v) ≤ r}`, over
all vertices `v` and reals `r ≥ 0`, is at most `c (|S| + 1)⁴`.

**Formalization Note** `d` is `dist` (infimum of walk lengths in `[0, ∞]`, `∞` if
unreachable); the radius ranges over `ℝ≥0`. The constant is universal (chosen before the graph,
the lengths and `S`). The distinct traces are counted as the members of the power set of `S` that
are realized. -/
theorem theorem_5_1 :
    ∃ c : ℕ, ∀ (n m : ℕ) (G : Graph n m), Planar G → ∀ (ℓ : Fin m → ℝ≥0) (S : Finset (Fin n)),
      (S.powerset.filter fun X => ∃ (v : Fin n) (r : ℝ≥0),
          X = S.filter fun u => dist G ℓ u v ≤ (r : ℝ≥0∞)).card ≤ c * (S.card + 1) ^ 4 := by sorry

end PlanarDFVSKernel
