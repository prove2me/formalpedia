-- Prove2me | Theorems.Thm_SparseDisc_theorem_8_1
-- name    : SparseDisc.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:17.64121+00:00
-- url     : https://prove2.me/theorems/01e74c4e-3bd5-441f-b500-e7e1c5b684f5
-- title:
--   Theorem 8.1 — $\mathrm{disc}(G) \le d+1$ for orderings with at most $d$ later neighbours
-- statement:
--   Let $(g_v, U_v)_{v \in V}$ be a 2-sparse instance such that the vertices of its graph $H(G)$ can be ordered so that every vertex has at most $d$ later neighbours. Then
--   $$
--   \operatorname{disc}(G) \le d + 1 .
--   $$
--   The bound does not depend on the vertex degrees or the bundle sizes; it gives the bound $1$ for $d = 0$ in Theorem 1.9.
--
--   **Formalization Note** The ordering is given by injective ranks; $d$ is a natural number.
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 8.1, p.29

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_instGraph
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_HasDegenOrdering

namespace SparseDisc

/-- **Theorem 8.1** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.29). Let `G` be a 2-sparse instance such that
the vertices of `H(G)` can be ordered so that every vertex has at most `d` later neighbours. Then
`disc(G) ≤ d + 1`. -/
theorem theorem_8_1 {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq ι]
    (g : V → Cube ι → ℝ) (U : V → Finset ι) (hg : IsInstance g U) (hU : IsTwoSparseSupp U)
    (d : ℕ) (hd : HasDegenOrdering (instGraph U) d) :
    InstDiscLE g ((d : ℝ) + 1) := by sorry

end SparseDisc
