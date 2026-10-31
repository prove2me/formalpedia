-- Prove2me | Theorems.Thm_PCLAssort_lemma_10_shift_feasible
-- name    : PCLAssort.lemma_10_shift_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:17.167244+00:00
-- url     : https://prove2.me/theorems/05e817c5-3a8c-485c-874a-70a142c288c6
-- title:
--   Lemma 10 — $x'$ keeps the knapsack tight and is feasible
-- statement:
--   Let $(x,y)$ be a basic feasible solution of the LP (9) with sizes $s_i>0$ and active knapsack constraint $\sum_is_ix_i=c$, and let $0<\delta<\tfrac12$ satisfy $x_i\in\{0,\delta,\tfrac12,1-\delta,1\}$ for all $i$ (Theorem 5). Then the vector $x'$ of step 2 of Algorithm 1 (equation (10)) satisfies
--
--   $$
--   \sum_is_ix'_i=\sum_is_ix_i=c,
--   $$
--
--   and $x'$ is feasible for LP (9) together with some $y'$.
--
--   Differences from the source:
--   - generalization: x comes from the optimal basic solution of step 1 of Algorithm 1 → x comes from any basic feasible solution (optimality not assumed); reason: the statement does not involve the objective; the optimal basic solution is a special case
--   - reading: sizes s_i, no sign stated → 0 < s_i; reason: the procedure divides by s_i, s_j and by S(V₁), S(V₂); the formulas are undefined otherwise
--   - encoding: basic feasible solution of LP (9) → extreme point of the feasible polytope in the joint (x, y) space; reason: for a polyhedron, basic feasible solutions are exactly its extreme points
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
--   - encoding: knapsack Σ_{i∈[n]} s_i x_i ≤ c in (9), with x_i ≤ 1 for i ∈ V → Σ over all i ∈ V; reason: for a generic graph V = [n]; same constraint
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 10, p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_LP9Feasible
import Definitions.Def_PCLAssort_alg1Shift

namespace PCLAssort

/-- Lemma 10 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794): the solution `x′` in step 2 of Algorithm 1 satisfies
`∑_i s_i x′_i = ∑_i s_i x_i = c` and is feasible to LP (9).

**Formalization Note.** The context of step 2: `(x, y)` is a basic feasible solution of LP (9) (an
extreme point), the knapsack is active, `δ` is a value given by Theorem 5 for `x`, and sizes are
positive. Feasibility of `x′` means that `(x′, y′)` is feasible for some `y′`. Optimality of `(x, y)`
is not assumed. -/
theorem lemma_10_shift_feasible {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V))
    (s : V → ℝ) (hs : ∀ i, 0 < s i) (c : ℝ) (p : (V → ℝ) × (V × V → ℝ))
    (hp : p ∈ Set.extremePoints ℝ (LP9Feasible E s c)) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hδ : ∀ i, p.1 i = 0 ∨ p.1 i = δ ∨ p.1 i = 1 / 2 ∨ p.1 i = 1 - δ ∨ p.1 i = 1)
    (hact : ∑ i, s i * p.1 i = c) :
    ∑ i, s i * alg1Shift s p.1 δ i = c ∧
      ∃ y' : V × V → ℝ, (alg1Shift s p.1 δ, y') ∈ LP9Feasible E s c := by sorry

end PCLAssort
