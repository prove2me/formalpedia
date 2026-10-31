-- Prove2me | Theorems.Thm_PCLAssort_theorem_5_half_integral
-- name    : PCLAssort.theorem_5_half_integral
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:53.535182+00:00
-- url     : https://prove2.me/theorems/c857ed34-44d3-4ec7-9726-3ad7d7a19419
-- title:
--   Theorem 5 — basic solutions of LP (9) take values in $\{0,\delta,\frac12,1-\delta,1\}$
-- statement:
--   Let $(V,E)$ be a directed graph without loops, $s_i\ge0$ sizes and $c\in\mathbb R$. Let $(x,y)$ be any basic feasible solution of the LP relaxation (9). Then
--
--   1. there is some $0<\delta<\tfrac12$ such that $x_i\in\{0,\delta,\tfrac12,1-\delta,1\}$ for all $i\in V$;
--   2. if $\sum_is_ix_i<c$, then $x_i\in\{0,\tfrac12,1\}$ for all $i\in V$.
--
--   This generalizes the half-integrality of max-dicut LP vertices under a cardinality constraint (Ageev et al. 2001) and is the structural input to Algorithm 1.
--
--   Differences from the source:
--   - reading: a directed graph (V, E) → a digraph without loops (e.1 ≠ e.2 for e ∈ E); reason: the paper's graphs G_z, G̃_z have no loops, and F(x) = Σ w_ij x_i(1 − x_j) agrees with the cut only without loops
--   - reading: sizes s_i of the knapsack family of §4, no sign stated → 0 ≤ s_i; reason: sizes are nonnegative in the paper's model
--   - encoding: basic feasible solution of LP (9) → extreme point of the feasible polytope in the joint (x, y) space; reason: for a polyhedron, basic feasible solutions are exactly its extreme points
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
--   - encoding: knapsack Σ_{i∈[n]} s_i x_i ≤ c in (9), with x_i ≤ 1 for i ∈ V → Σ over all i ∈ V; reason: for a generic graph V = [n]; same constraint
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Theorem 5, p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_LP9Feasible

namespace PCLAssort

/-- Theorem 5 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794): let `(x, y)` be any basic feasible solution to the LP relaxation (9).
Then there is some value `0 < δ < 1/2` such that `x_i ∈ {0, δ, 1/2, 1 − δ, 1}` for all `i ∈ V`.
Moreover, if `∑_i s_i x_i < c`, then `x_i ∈ {0, 1/2, 1}` for all `i ∈ V`.

**Formalization Note.** "Basic feasible solution" is an extreme point of the feasible polytope of
LP (9) in the joint `(x, y)` space. The digraph has no loops. Sizes `s_i ≥ 0`, `c` any real. -/
theorem theorem_5_half_integral {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (s : V → ℝ) (hs : ∀ i, 0 ≤ s i) (c : ℝ)
    (p : (V → ℝ) × (V × V → ℝ)) (hp : p ∈ Set.extremePoints ℝ (LP9Feasible E s c)) :
    (∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ i, p.1 i = 0 ∨ p.1 i = δ ∨ p.1 i = 1 / 2 ∨ p.1 i = 1 - δ ∨ p.1 i = 1) ∧
    (∑ i, s i * p.1 i < c → ∀ i, p.1 i = 0 ∨ p.1 i = 1 / 2 ∨ p.1 i = 1) := by sorry

end PCLAssort
