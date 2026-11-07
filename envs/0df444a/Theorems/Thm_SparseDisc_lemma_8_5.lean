-- Prove2me | Theorems.Thm_SparseDisc_lemma_8_5
-- name    : SparseDisc.lemma_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:21.435709+00:00
-- url     : https://prove2.me/theorems/06063181-2e95-45f4-8715-77494197111a
-- title:
--   Lemma 8.5 — $c$-good graphs are exactly the graphs whose instances have discrepancy at most $c$
-- statement:
--   Let $c \ge 1$ and let $G$ be a simple graph on a finite vertex set $V$. Then $G$ is $c$-good if and only if every 2-sparse instance $(g_v, U_v)_{v \in V}$ whose graph $H$ is a subgraph of $G$ has discrepancy at most $c$. Moreover, a $c$-good graph is $c'$-good for every $c' \ge c$.
--
--   The lemma converts discrepancy bounds into the solvability of constraint systems with coarse constraints, the form in which the deletion arguments of Section 8 run.
--
--   **Formalization Note** The range $c \ge 1$ is the standing range of $c$-coarseness (Definition 8.2). Instances and constraint systems range over every finite item type.
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 8.5, p.30

import Mathlib
import Definitions.Def_SparseDisc_IsCGood
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_InstDiscLE

namespace SparseDisc

/-- **Lemma 8.5** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), p.30). A simple graph `G` on `V` is `c`-good iff
every 2-sparse instance `(g_v, U_v)_{v ∈ V}` whose graph is a subgraph of `G` has discrepancy at
most `c`; a `c`-good graph is `c'`-good for every `c' ≥ c`.

**Formalization Note** `c ≥ 1` is the standing range of "`c`-coarse" (Definition 8.2) and is a
hypothesis. Instances range over every finite item type. -/
theorem lemma_8_5 {V : Type} [Fintype V] (G : SimpleGraph V) (c : ℝ) (hc : 1 ≤ c) :
    (IsCGood G c ↔
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : V → Cube ι → ℝ) (U : V → Finset ι),
        IsInstance g U → IsTwoSparseSupp U → instGraph U ≤ G → InstDiscLE g c) ∧
    ∀ c' : ℝ, c ≤ c' → IsCGood G c → IsCGood G c' := by sorry

end SparseDisc
