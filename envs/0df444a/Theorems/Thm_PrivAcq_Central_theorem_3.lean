-- Prove2me | Theorems.Thm_PrivAcq_Central_theorem_3
-- name    : PrivAcq.Central.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:35.010676+00:00
-- url     : https://prove2.me/theorems/ff8519e5-38e4-4b77-9dce-813842ab8b54
-- title:
--   Theorem 3, p. 18 — under Assumption 1, $\varepsilon^*_i = y^*_i$ and weights $y^*_i/\sum_j y^*_j$ ($y^*$ solving (23)) give the optimal central mechanism
-- statement:
--   Consider the central-privacy data acquisition model under the standing assumptions, and suppose Assumption 1 holds: every virtual cost $\psi_i(c) = c + F_i(c)/f_i(c)$ is increasing. For every type profile $c$ let $y^*(c) = (y^*_1(c),\dots,y^*_n(c))$ be an optimal solution of
--   $$
--   \min_{y}\; \frac{n+1}{\big(\sum_{j=1}^n y_j\big)^2}\Big(2 + \sum_{i=1}^n y_i^2\,\mathrm{VAR}\Big) + \sum_{i=1}^n \psi_i(c_i)\,y_i \quad \text{s.t. } y_i \ge 0 \text{ for all } i, \qquad (23)
--   $$
--   chosen measurably in $c$. Let the mechanism $M^*$ use privacy losses $\varepsilon^*_i(c) = y^*_i(c)$, the estimator weights $w^*_i(c) = y^*_i(c)/\sum_{j=1}^n y^*_j(c)$ and Laplace parameter $\eta^*(c) = \sum_j y^*_j(c)$, and the payments (19) with $d_i = 0$. Then
--
--   1. $M^*$ is an admissible mechanism of class (22), incentive compatible (17) and individually rational (18); and
--   2. its expected platform cost $\mathbb E_c[\mathrm{MSE}(c) + \sum_i t_i(c)]$ is at most that of every admissible mechanism of class (22) that is incentive compatible and individually rational.
--
--   So the optimal privacy loss level is $\varepsilon^*_i(c) = y^*_i$, and user $i$'s data receives weight $y^*_i/\sum_j y^*_j$ in the platform's estimator.
--
--   **Formalization Note** The theorem is proved for every measurable selection of minimizers (the minimizer need not be unique); it does not claim that every optimal mechanism coincides with $M^*$. The feasible set of (23) adds $\sum_j y_j > 0$ (at $y = 0$ the objective is undefined). Model conventions (compact type support with $a_i > 0$, no differentiability or sign constraint on payments, strictly increasing $\psi_i$) are listed in `PrivAcq.Central.Model`.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 18, Theorem 3 and (23); proof pp. 44–45

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

namespace PrivAcq.Central

open MeasureTheory

theorem theorem_3 {n : ℕ} (S : Setting n) (hS : S.Standing) (hA1 : S.Assumption1)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types, IsOpt23 S c (ystar c)) :
    Admissible S (optMech S ystar) ∧ IC S (optMech S ystar) ∧ IR S (optMech S ystar) ∧
      ∀ M : Mech n, Admissible S M → IC S M → IR S M →
        objective S (optMech S ystar) ≤ objective S M := by sorry

end PrivAcq.Central
