-- Prove2me | Theorems.Thm_PCLAssort_lemma_12_inactive_half
-- name    : PCLAssort.lemma_12_inactive_half
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:05.821988+00:00
-- url     : https://prove2.me/theorems/6e4dcc15-1946-48ac-b485-3b2b772ca138
-- title:
--   Lemma 12 — inactive knapsack: $F(x)\ge 0.5\,L(x)$
-- statement:
--   Let $(V,E)$ be a directed graph without loops, with weights $w_{ij}\ge0$ on $E$, sizes $s_i\ge0$ and capacity $c$, and let $(x,y)$ be an optimal basic solution of the LP (9) with $\sum_is_ix_i<c$ (the constraint is not active). Then
--
--   $$
--   F(x)\ge 0.5\cdot L(x).
--   $$
--
--   Differences from the source:
--   - reading: a directed graph (V, E) → a digraph without loops (e.1 ≠ e.2 for e ∈ E); reason: the paper's graphs G_z, G̃_z have no loops, and F(x) = Σ w_ij x_i(1 − x_j) agrees with the cut only without loops
--   - reading: sizes s_i of the knapsack family of §4, no sign stated → 0 ≤ s_i; reason: sizes are nonnegative in the paper's model
--   - encoding: basic feasible solution of LP (9) → extreme point of the feasible polytope in the joint (x, y) space; reason: for a polyhedron, basic feasible solutions are exactly its extreme points
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
--   - reading: edge weights w : E → ℝ (Definition 1: "usually assumed" nonnegative) → 0 ≤ w e for e ∈ E; reason: p.794: "it suffices to consider instances with nonnegative edge-weights"; Algorithm 1 is stated for that setting (G̃_z)
--   - encoding: knapsack Σ_{i∈[n]} s_i x_i ≤ c in (9), with x_i ≤ 1 for i ∈ V → Σ over all i ∈ V; reason: for a generic graph V = [n]; same constraint
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 12, p.795 (PDF p.11)

import Mathlib
import Definitions.Def_PCLAssort_LP9Feasible
import Definitions.Def_PCLAssort_IsLP9Optimal
import Definitions.Def_PCLAssort_dicutF
import Definitions.Def_PCLAssort_dicutL

namespace PCLAssort

/-- Lemma 12 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.795): if the constraint `∑_i s_i x_i ≤ c` is not active, then
`F(x) ≥ 0.5 · L(x)`.

**Formalization Note.** The context of Algorithm 1: `(x, y)` is an optimal basic solution of LP (9)
for a loopless digraph with nonnegative weights on `E`; sizes are nonnegative. -/
theorem lemma_12_inactive_half {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → ℝ) (hw : ∀ e ∈ E, 0 ≤ w e)
    (s : V → ℝ) (hs : ∀ i, 0 ≤ s i) (c : ℝ) (p : (V → ℝ) × (V × V → ℝ))
    (hp : p ∈ Set.extremePoints ℝ (LP9Feasible E s c)) (hopt : IsLP9Optimal E w s c p)
    (hinact : ∑ i, s i * p.1 i < c) :
    (0.5 : ℝ) * dicutL E w p.1 ≤ dicutF E w p.1 := by sorry

end PCLAssort
