-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_5_2_minimal_attachment_triangle
-- name    : SubmodPerfect.lemma_5_2_minimal_attachment_triangle
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:44.114467+00:00
-- url     : https://prove2.me/theorems/435fbfc8-20d8-4bd7-bd9f-4c3d29852fc7
-- title:
--   Lemma 5.2 — a minimal attachment to a triangle forms a proper, universal or twin wheel
-- statement:
--   Let $G$ be a prism-free perfect graph and $x_1x_2x_3$ a triangle of $G$. Let $H\subseteq V(G)\setminus\{x_1,x_2,x_3\}$ induce a connected subgraph that contains a neighbour of each $x_i$ and no vertex complete to $\{x_1,x_2,x_3\}$, and suppose $H$ is inclusion-wise minimal with these properties. Then there are distinct $i,j,k$ with $\{i,j,k\}=\{1,2,3\}$ such that
--
--   1. $H\cup\{x_i,x_j\}$ is the vertex set of a hole $H'$, and $(H',x_k)$ is a proper, a universal or a twin wheel; and
--   2. if each of $x_1,x_2,x_3$ has a unique neighbour in $H$, then for some $\ell\in\{i,j\}$, $x_\ell$ and $x_k$ have a common neighbour in $H$.
--
--   This is the structural step behind the paw theorem (Theorem 5.6).
--
--   Differences from the source:
--   - encoding: the triangle x1x2x3 and the subgraph H → x : Fin 3 → V and a vertex set H; the hole H′ is a cyclic list with vertex set H ∪ {x_i, x_j}; reason: Lean convention; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 5.2, p.16

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 5.2, p.16.

Let `x₁x₂x₃` be a triangle in a prism-free perfect graph `G`. Assume that `H` is a connected
induced subgraph of `G \ {x₁, x₂, x₃}` containing a neighbour of each `xᵢ`, no vertex of `H` is
complete to `{x₁, x₂, x₃}`, and `V(H)` is minimal subject to inclusion. Then for some
`{i, j, k} = {1, 2, 3}`, `H ∪ {xᵢ, xⱼ}` is a hole `H′` and `(H′, x_k)` is a proper, a universal,
or a twin wheel. Moreover, if each `xᵢ` has a unique neighbour in `H`, then `x_ℓ` and `x_k` have
a common neighbour in `H` for some `ℓ ∈ {i, j}`.

**Formalization Note.** The triangle is `x : Fin 3 → V`. `H` is a vertex set; minimality is
among all subsets of `H` with every stated property. The hole `H′` is a cyclic list whose vertex
set is `H ∪ {xᵢ, xⱼ}`. -/
theorem lemma_5_2_minimal_attachment_triangle {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hperf : StrongPerfectGraph.Main.IsPerfect G) (hprism : IsPrismFree G)
    (x : Fin 3 → V) (htri : ∀ i j, i ≠ j → G.Adj (x i) (x j))
    (H : Finset V) (hHx : ∀ i, x i ∉ H) (hHconn : (G.induce (H : Set V)).Connected)
    (hHnbr : ∀ i, ∃ y ∈ H, G.Adj (x i) y) (hHcomp : ∀ y ∈ H, ¬ ∀ i, G.Adj (x i) y)
    (hHmin : ∀ H' : Finset V, H' ⊆ H → (G.induce (H' : Set V)).Connected →
      (∀ i, ∃ y ∈ H', G.Adj (x i) y) → (∀ y ∈ H', ¬ ∀ i, G.Adj (x i) y) → H' = H) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ∃ H' : List V, StrongPerfectGraph.OddPrism.IsHole G H' ∧
        H'.toFinset = H ∪ {x i, x j} ∧
        (IsProperWheel G H' (x k) ∨ IsUniversalWheel G H' (x k) ∨ IsTwinWheel G H' (x k)) ∧
        ((∀ m, ∃! y, y ∈ H ∧ G.Adj (x m) y) →
          ∃ l, (l = i ∨ l = j) ∧ ∃ y ∈ H, G.Adj (x l) y ∧ G.Adj (x k) y) := by sorry

end SubmodPerfect
