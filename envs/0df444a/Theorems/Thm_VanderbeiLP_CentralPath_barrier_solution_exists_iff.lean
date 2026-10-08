-- Prove2me | Theorems.Thm_VanderbeiLP_CentralPath_barrier_solution_exists_iff
-- name    : VanderbeiLP.CentralPath.barrier_solution_exists_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:35:53.071796+00:00
-- url     : https://prove2.me/theorems/c43d20fb-2a73-4a06-a6a1-7d570ff2a760
-- title:
--   Theorem 17.2 — the barrier problem has a solution iff primal and dual have nonempty interior
-- statement:
--   Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and fix a barrier parameter $\mu > 0$. The barrier problem (17.2) is
--
--   $$\text{maximize } f(x, w) = c^T x + \mu \sum_{j=1}^n \log x_j + \mu \sum_{i=1}^m \log w_i \quad \text{subject to } Ax + w = b,$$
--
--   over the domain $x > 0$, $w > 0$ where the logarithms are finite. Then the barrier problem has a solution — a pair $(x, w)$ in this domain at which $f$ attains its maximum over the domain — **if and only if** both the primal feasible region $\{(x, w) : Ax + w = b,\ x, w \ge 0\}$ and the dual feasible region $\{(y, z) : A^T y - z = c,\ y, z \ge 0\}$ have nonempty interior, i.e.
--
--   $$\exists\, (\bar x, \bar w):\ A\bar x + \bar w = b,\ \bar x > 0,\ \bar w > 0 \qquad\text{and}\qquad \exists\, (\bar y, \bar z):\ A^T\bar y - \bar z = c,\ \bar y > 0,\ \bar z > 0.$$
--
--   This is the existence half of the theory of the central path: together with the uniqueness of the barrier maximizer it shows that the central path is defined for every $\mu > 0$ exactly when both problems are strictly feasible.
--
--   **Formalization Note** "Nonempty interior" is read as in the book's proof (p. 265): a feasible point with every component strictly positive; the topological interior of the primal region in $\mathbb{R}^{n+m}$ is empty for $m \ge 1$. "A solution to the barrier problem" is a maximizer of $f$ over $\{Ax + w = b,\ x > 0,\ w > 0\}$, so a solution is itself a strictly positive primal point. The book calls the "only if" half trivial and does not prove it; it is part of the statement. The theorem is stated for one fixed $\mu > 0$ (p. 258: "the parameter $\mu$, which we assume to be positive").
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 265, Theorem 17.2 and the first paragraph of its proof (PDF p. 275); barrier problem (17.2), p. 258 (PDF p. 268)

import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Theorem 17.2 (p. 265). For a fixed barrier parameter `μ > 0`, the barrier problem (17.2) has
a solution if and only if both the primal and the dual feasible regions have nonempty interior
(a primal feasible `(x̄, w̄)` with `x̄, w̄ > 0` and a dual feasible `(ȳ, z̄)` with `ȳ, z̄ > 0`). -/
theorem barrier_solution_exists_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (hμ : 0 < μ) :
    (∃ (x : Fin n → ℝ) (w : Fin m → ℝ), IsBarrierSolution A b c μ x w) ↔
      PrimalStrictlyFeasible A b ∧ DualStrictlyFeasible A c := by sorry

end VanderbeiLP.CentralPath
