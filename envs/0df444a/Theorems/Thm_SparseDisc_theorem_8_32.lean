-- Prove2me | Theorems.Thm_SparseDisc_theorem_8_32
-- name    : SparseDisc.theorem_8_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:50.88854+00:00
-- url     : https://prove2.me/theorems/41595700-5ba3-4fcd-8e2d-6c3bcea4f28b
-- title:
--   Theorem 8.32 — orientations: $\mathrm{disc}(G) \le k+1$, $p(H)+1$, $\lceil\Delta/2\rceil+1$
-- statement:
--   Let $G$ be a 2-sparse instance with graph $H = H(G)$.
--
--   1. If $H$ has an orientation in which every vertex has in-degree at most $k$, then $\operatorname{disc}(G) \le k + 1$.
--   2. Consequently $\operatorname{disc}(G) \le p(H) + 1$, where $p(H) = \max_{H'} \lceil |E(H')| / |V(H')| \rceil$ over the nonempty subgraphs $H'$ of $H$.
--   3. In particular, if every function has at most $\Delta$ distinct neighbours, then
--   $$
--   \operatorname{disc}(G) \le \lceil \Delta / 2 \rceil + 1 .
--   $$
--
--   **Formalization Note** An orientation is a relation directing every edge exactly once; the number of distinct neighbours is the degree in $H$; $\lceil \Delta/2 \rceil$ is the natural number $(\Delta + 1)/2$.
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 8.32, p.43

import Mathlib
import Definitions.Def_SparseDisc_IsOrientation
import Definitions.Def_SparseDisc_pseudoarboricity
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_instGraph
import Definitions.Def_SparseDisc_InstDiscLE

namespace SparseDisc

open Classical in
/-- **Theorem 8.32** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.43). Let `G` be a 2-sparse instance. If `H(G)`
has an orientation in which every vertex has in-degree at most `k`, then `disc(G) ≤ k + 1`.
Consequently `disc(G) ≤ p(H) + 1`; in particular, if every function has at most `Δ` distinct
neighbours, then `disc(G) ≤ ⌈Δ/2⌉ + 1`.

**Formalization Note** The in-degree of `v` is the number of `u` with `D u v`; `⌈Δ/2⌉` is the
natural number `(Δ + 1) / 2`; the number of distinct neighbours is the degree in `H(G)`. -/
theorem theorem_8_32 {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq ι]
    (g : V → Cube ι → ℝ) (U : V → Finset ι) (hg : IsInstance g U) (hU : IsTwoSparseSupp U) :
    (∀ (k : ℕ) (D : V → V → Prop), IsOrientation (instGraph U) D →
      (∀ v, (Finset.univ.filter (fun u => D u v)).card ≤ k) → InstDiscLE g ((k : ℝ) + 1)) ∧
    InstDiscLE g ((pseudoarboricity (instGraph U) : ℝ) + 1) ∧
    (∀ Δ : ℕ, (∀ v, (instGraph U).degree v ≤ Δ) →
      InstDiscLE g ((((Δ + 1) / 2 : ℕ) : ℝ) + 1)) := by sorry

end SparseDisc
