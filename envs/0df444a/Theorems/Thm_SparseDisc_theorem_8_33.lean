-- Prove2me | Theorems.Thm_SparseDisc_theorem_8_33
-- name    : SparseDisc.theorem_8_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:56.828083+00:00
-- url     : https://prove2.me/theorems/2692fc3e-1526-41ea-8429-9aa9cbd0bb78
-- title:
--   Theorem 8.33 — 2-degenerate plus $c-2$ forests is $c$-good; planar patterns have $\mathrm{disc} \le 3$
-- statement:
--   Let $c \ge 2$ be an integer.
--
--   1. Every graph that is the union of a 2-degenerate graph and $c - 2$ forests is $c$-good.
--   2. So $\operatorname{disc}(G) \le c$ for every 2-sparse instance $G$ whose graph $H(G)$ is a subgraph of such a graph.
--   3. In particular, every 2-sparse instance with planar graph $H(G)$ has $\operatorname{disc}(G) \le 3$.
--
--   **Formalization Note** The union is the supremum of graphs on one vertex set (a forest on part of the vertices is a spanning forest with isolated vertices added). Planarity is the published `RobertsonSeymour1986.GM5.IsPlanar` (a crossing-free drawing in the plane by simple arcs).
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
--   - encoding: union of a 2-degenerate graph and c − 2 forests → supremum D ⊔ ⨆ i, F i of graphs on one vertex type; reason: Lean convention; a union of graphs on subsets of V is a union of spanning graphs with isolated vertices added
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 8.33, p.43

import Mathlib
import Definitions.Def_SparseDisc_HasDegenOrdering
import Definitions.Def_SparseDisc_IsCGood
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_instGraph
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace SparseDisc

/-- **Theorem 8.33** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.43). Let `c ≥ 2`. Every graph that is the
union of a 2-degenerate graph and `c − 2` forests is `c`-good; so `disc(G) ≤ c` whenever `H(G)` is a
subgraph of such a graph. In particular, planar patterns have `disc(G) ≤ 3`.

**Formalization Note** The union is the supremum `D ⊔ ⨆ i, F i` of graphs on one vertex type (a
forest on fewer vertices is a spanning forest with isolated vertices added); `c` is a natural
number; planarity is the published `RobertsonSeymour1986.GM5.IsPlanar`. -/
theorem theorem_8_33 (c : ℕ) (hc : 2 ≤ c) :
    (∀ (V : Type) [Fintype V] (D : SimpleGraph V) (F : Fin (c - 2) → SimpleGraph V),
      HasDegenOrdering D 2 → (∀ i, (F i).IsAcyclic) → IsCGood (D ⊔ ⨆ i, F i) (c : ℝ)) ∧
    (∀ (V ι : Type) [Fintype V] [Fintype ι] [DecidableEq ι] (g : V → Cube ι → ℝ)
      (U : V → Finset ι), IsInstance g U → IsTwoSparseSupp U →
      (∃ (D : SimpleGraph V) (F : Fin (c - 2) → SimpleGraph V), HasDegenOrdering D 2 ∧
        (∀ i, (F i).IsAcyclic) ∧ instGraph U ≤ D ⊔ ⨆ i, F i) →
      InstDiscLE g (c : ℝ)) ∧
    (∀ (V ι : Type) [Fintype V] [Fintype ι] [DecidableEq ι] (g : V → Cube ι → ℝ)
      (U : V → Finset ι), IsInstance g U → IsTwoSparseSupp U →
      RobertsonSeymour1986.GM5.IsPlanar (instGraph U) → InstDiscLE g 3) := by sorry

end SparseDisc
