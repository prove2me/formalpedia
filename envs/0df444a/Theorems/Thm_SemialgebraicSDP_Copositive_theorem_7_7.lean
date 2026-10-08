-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_theorem_7_7
-- name    : SemialgebraicSDP.Copositive.theorem_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:40.20467+00:00
-- url     : https://prove2.me/theorems/621f5df0-dd49-4617-86e2-6beb6b3c360a
-- title:
--   Theorem 7.7, p. 318 — a feasible solution of the SDPs (7.7) makes $P_1(z) \ge 0$ and $M$ copositive; (7.6) implies (7.7) is feasible
-- statement:
--   Let $M = (m_{ij})$ be a real symmetric $n \times n$ matrix and $P_1(z) = \sum_{i,j,k} m_{ij} z_i^2 z_j^2 z_k^2$. Consider the SDPs (7.7) in $n$ symmetric matrices $\Lambda^1, \dots, \Lambda^n \in \mathcal S^n$:
--   $$
--   \begin{aligned}
--   M - \Lambda^i &\succeq 0, && i = 1, \dots, n,\\
--   \Lambda^i_{ii} &= 0, && i = 1, \dots, n,\\
--   \Lambda^i_{jj} + \Lambda^j_{ji} + \Lambda^j_{ij} &= 0, && i \ne j,\\
--   \Lambda^i_{jk} + \Lambda^j_{ki} + \Lambda^k_{ij} &\ge 0, && i, j, k \text{ pairwise distinct}.
--   \end{aligned}
--   $$
--   Then:
--
--   1. If (7.7) has a feasible solution, then $P_1(z) \ge 0$ for every $z \in \mathbb R^n$, and $M$ is copositive ($x^T M x \ge 0$ whenever $x_i \ge 0$ for all $i$).
--   2. The test is at least as powerful as condition (7.6): if $M = P + N$ with $P \succeq 0$ and $n_{ij} \ge 0$ for all $i, j$, then (7.7) has a feasible solution.
--
--   Theorem 7.7 is the first level ($r = 1$) of a hierarchy of semidefinite programming tests for copositivity, a property for which deciding that a given matrix is *not* copositive is NP-complete. It gives an explicit semidefinite program that certifies copositivity of every matrix covered by the classical decomposition test (7.6).
--
--   **Formalization Note** "At least as powerful as condition (7.6)" is formalized as the implication (7.6) $\Rightarrow$ (7.7) feasible, i.e. every matrix certified by (7.6) is also certified by (7.7). "$i \ne j \ne k$" is read as pairwise distinct (see the definition `Feasible77`). Copositivity is the published `MurtyKabadi.Reduction.Copositive`.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 318, Theorem 7.7

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_SemialgebraicSDP_Copositive_Forms
import Definitions.Def_SemialgebraicSDP_Copositive_Certificates

namespace SemialgebraicSDP.Copositive

open MvPolynomial

/-- Theorem 7.7 (Parrilo 2003, p. 318). Let `M` be a real symmetric `n × n` matrix. If the
SDPs (7.7) have a feasible solution, then `P₁(z)` is nonnegative, and therefore `M` is
copositive. Furthermore, the test is at least as powerful as condition (7.6): whenever (7.6)
holds, (7.7) is feasible. -/
theorem theorem_7_7 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (Feasible77 M →
        (∀ z : Fin n → ℝ, 0 ≤ eval z (formP1 M)) ∧ MurtyKabadi.Reduction.Copositive M) ∧
      (Cond76 M → Feasible77 M) := by sorry

end SemialgebraicSDP.Copositive
