-- Prove2me | Theorems.Thm_SmaleNinth_klee_minty_dantzig_exponential
-- name    : SmaleNinth.klee_minty_dantzig_exponential
-- status  : Proved
-- author  : @ORdos
-- created : 2026-09-06T15:25:58.466275+00:00
-- url     : https://prove2.me/theorems/d12dec36-c2f7-4f2c-b023-6086782091b6
-- title:
--   Klee–Minty: Dantzig's rule takes $2^n-1$ pivots
-- statement:
--   The simplex method moves between adjacent vertices of the feasible region, at each step admitting some column with negative reduced cost into the basis and expelling a row determined by the ratio test. A **pivoting rule** resolves the remaining freedom; **Dantzig's rule** — the historical and still most familiar choice — enters a column of most negative reduced cost.
--
--   This theorem states that on the $n$-dimensional Klee–Minty cube in standard form, with $n$ equality constraints and $2n$ nonnegative variables, that rule can be made to traverse the entire cube. Precisely: for every $n \ge 1$ there is a sequence of basis-and-point pairs
--
--   $$(B_0, x_0),\, (B_1, x_1),\, \dots,\, (B_{2^n-1}, x_{2^n-1})$$
--
--   such that $(B_0, x_0)$ is the all-slack basis together with its basic feasible solution (every original variable $0$, every slack $s_i = 100^{\,i}$); every $(B_k, x_k)$ with $k \le 2^n - 1$ is a legitimate simplex state, meaning the chosen columns are linearly independent, the point is feasible, and it vanishes off the basis; each of the $2^n - 1$ consecutive transitions $(B_k, x_k) \to (B_{k+1}, x_{k+1})$ is a Dantzig pivot; and the terminal basis $B_{2^n-1}$ is optimal, in the sense that every nonbasic column has nonnegative reduced cost, so no further pivot is available.
--
--   **Why the statement is existential.** A worst-case lower bound is a claim about *some* run, not about every run: Dantzig's rule leaves ties unresolved, and the assertion is that a run consistent with the rule attains the full length $2^n - 1$, which is one less than the number $2^n$ of vertices of the cube. Since the instance has $n$ constraints and $2n$ variables, the number of pivots is exponential in the size of the input, so the simplex method under Dantzig's rule is not a polynomial-time algorithm.
--
--   **Scope.** The result is about this rule on this family only. Exponential families are known for essentially every other classical deterministic rule, and subexponential lower bounds for the randomized ones; none of that is asserted here, and each would be a separate statement over the same simplex development.
--
--   **Convention.** Bases are recorded as injections from row indices into column indices and points as vectors in $\mathbb{R}^{2n}$, with $0$-based indexing; the optimality of the terminal state is a condition on the reduced costs at $B_{2^n-1}$, not a separate claim that $x_{2^n-1}$ minimizes the objective, which follows from it by the standard optimality criterion.
-- source:
--   V. Klee, G.J. Minty, How good is the simplex algorithm?, in: Inequalities III (O. Shisha, ed.), Academic Press 1972, pp. 159-175. Presentation followed: V. Chvatal, Linear Programming, Freeman 1983, Chapter 4, problem (4.6) and the surrounding analysis (2^n - 1 iterations from the all-slack dictionary under the largest-coefficient rule).

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_SimplexPivot
import Definitions.Def_SmaleNinth_KleeMinty

/-!
The Klee–Minty exponential lower bound for Dantzig's pivoting rule.

Source: V. Klee, G.J. Minty, *How good is the simplex algorithm?*, in:
Inequalities III (O. Shisha, ed.), Academic Press 1972, pp. 159–175;
presentation of V. Chvátal, *Linear Programming*, Freeman 1983, Chapter 4:
on problem (4.6) — here `kleeMintyA/b/c` in standard form — the simplex
method with Dantzig's largest-coefficient entering rule, started from the
all-slack dictionary, performs exactly `2ⁿ − 1` iterations.

Formalized as the worst-case lower bound: there exists an admissible
trajectory of `2ⁿ − 1` consecutive Dantzig pivots from the all-slack basic
feasible solution whose final state is optimal-terminal. (Together with the
platform's simplex development this witnesses that Dantzig's rule is not
polynomial: the instance has `2n` variables, `n` constraints, and forces
`2ⁿ − 1` pivots.)
-/

open Matrix LinearOptimization

/-- **Klee–Minty 1972** (Chvátal, Chapter 4). On the `n`-dimensional
Klee–Minty cube in standard form, Dantzig's rule admits a run of `2ⁿ − 1`
simplex pivots from the all-slack basic feasible solution, ending in an
optimal terminal state — the simplex method with Dantzig's entering rule
takes exponentially many iterations in the worst case. -/

theorem SmaleNinth.klee_minty_dantzig_exponential (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ℕ → (Fin n ↪ Fin (2 * n)) × (Fin (2 * n) → ℝ),
      (f 0).1 = kleeMintySlackBasis n ∧
      (f 0).2 = kleeMintySlackSolution n ∧
      (∀ k ≤ 2 ^ n - 1,
        IsSimplexState (kleeMintyA n) (kleeMintyb n) (f k).1 (f k).2) ∧
      (∀ k < 2 ^ n - 1,
        IsDantzigPivot (kleeMintyA n) (kleeMintyc n) (f k).1 (f k).2
          (f (k + 1)).1 (f (k + 1)).2) ∧
      IsSimplexOptimalTerminal (kleeMintyA n) (kleeMintyc n)
        (f (2 ^ n - 1)).1 := by sorry
