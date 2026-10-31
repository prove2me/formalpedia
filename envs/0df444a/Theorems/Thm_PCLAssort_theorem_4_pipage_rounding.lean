-- Prove2me | Theorems.Thm_PCLAssort_theorem_4_pipage_rounding
-- name    : PCLAssort.theorem_4_pipage_rounding
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:05.239024+00:00
-- url     : https://prove2.me/theorems/d0b115e8-eb08-43d4-90e7-05a15f5fd23d
-- title:
--   Theorem 4 — pipage rounding with a knapsack constraint
-- statement:
--   Let $V$ be a finite set, $s_i>0$ sizes, $c$ a capacity, $F:[0,1]^V\to\mathbb R_{\ge0}$ continuous and $L$ a function with $L(x)=F(x)$ for all $x\in\{0,1\}^V$ (a "nice" relaxation). Let $x$ be a solution of (8), i.e. $x\in[0,1]^V$ with $\sum_is_ix_i\le c$. Suppose that $F$ has the $\epsilon$-convexity property and that $F(x)\ge\alpha L(x)$ for some $\alpha<1$. Then
--
--   1. pipage rounding started at $x$ terminates: there is a complete run from $x$;
--   2. every complete run ends at a solution $x^*$ of (8) with at most one fractional variable and
--
--   $$
--   F(x^*)\ge F(x)\ge\alpha\cdot L(x);
--   $$
--
--   3. if moreover $s_i=1$ for all $i$, $c$ is a nonnegative integer and the knapsack constraint is active for $x$, then $x^*$ is integral.
--
--   Differences from the source:
--   - generalization: L is a linear function → L is any function with L = F on {0,1}^V; reason: the statement uses L only through F(x) ≥ αL(x); the paper itself applies it with the nonlinear L(x) = Σ w_ij min{x_i, 1 − x_j}; a linear L is a special case
--   - generalization: we can find a solution x* with these properties → a complete pipage run exists, and every complete run ends at such an x*; reason: existence is the first conjunct; the bound for every run specializes to the bound for the one found
--   - reading: sizes s_i, no sign stated → 0 < s_i; reason: the procedure divides by s_i, s_j and by S(V₁), S(V₂); the formulas are undefined otherwise
--   - reading: c ∈ ℤ₊ → c = k for some k ∈ ℕ; reason: includes c = 0, so the clause covers the positive-integer reading
--   - encoding: x* is a solution of (8) → x* ∈ [0,1]^V and Σ s_i x*_i ≤ c; reason: definition of (8)
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Theorem 4, p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_EpsConvex
import Definitions.Def_PCLAssort_FLLowerBound
import Definitions.Def_PCLAssort_PipageRun
import Definitions.Def_PCLAssort_fracCoords

namespace PCLAssort

/-- Theorem 4 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794), pipage rounding. Consider an instance of problem (7) with a "nice"
relaxation (8) and any solution `x` to (8). Suppose that `F` satisfies the ε-convexity property and
the F/L lower bound property for `x` and some `α < 1`. Then we can find a solution `x*` with at most
one fractional variable such that `F(x*) ≥ F(x) ≥ α · L(x)`. Furthermore, if `s_i = 1` for all `i`,
`c ∈ ℤ₊` and the knapsack constraint is active for `x`, then `x*` is integral. (The starting point
`x` is the binder `xbar`, the `x̄` of the pipage procedure on the same page.)

**Formalization Note.** `F : [0,1]^V → ℝ₊` is continuous; `L` agrees with `F` on `{0,1}^V` (nice
relaxation). Sizes are positive (the procedure divides by `s_i`, `s_j`). "We can find" is stated in the
stronger form: a complete pipage run from `x̄` exists, and every complete run ends at such an `x*`.
`ℤ₊` is read as `ℕ`. -/
theorem theorem_4_pipage_rounding {V : Type} [Fintype V] [DecidableEq V]
    (F L : (V → ℝ) → ℝ) (s : V → ℝ) (c α : ℝ)
    (hFcont : ContinuousOn F (Set.Icc 0 1)) (hFnn : ∀ x ∈ Set.Icc (0 : V → ℝ) 1, 0 ≤ F x)
    (hnice : ∀ x : V → ℝ, (∀ i, x i = 0 ∨ x i = 1) → L x = F x)
    (hs : ∀ i, 0 < s i) (xbar : V → ℝ) (hxbar : xbar ∈ Set.Icc (0 : V → ℝ) 1)
    (hxbarc : ∑ i, s i * xbar i ≤ c)
    (hconv : EpsConvex s F) (hFL : FLLowerBound F L α xbar) (hα : α < 1) :
    (∃ xstar, PipageRun s F xbar xstar) ∧
    ∀ xstar, PipageRun s F xbar xstar →
      xstar ∈ Set.Icc (0 : V → ℝ) 1 ∧ ∑ i, s i * xstar i ≤ c ∧ (fracCoords xstar).card ≤ 1 ∧
      F xbar ≤ F xstar ∧ α * L xbar ≤ F xbar ∧
      ((∀ i, s i = 1) → (∃ k : ℕ, c = k) → ∑ i, s i * xbar i = c →
        ∀ i, xstar i = 0 ∨ xstar i = 1) := by sorry

end PCLAssort
