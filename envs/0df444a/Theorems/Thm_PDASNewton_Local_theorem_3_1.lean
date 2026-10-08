-- Prove2me | Theorems.Thm_PDASNewton_Local_theorem_3_1
-- name    : PDASNewton.Local.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:18.806935+00:00
-- url     : https://prove2.me/theorems/fc43cbcb-d6a4-487c-9543-5bd914ccc640
-- title:
--   Theorem 3.1, p. 7 — for a P-matrix the primal-dual active set method converges superlinearly from x⁰ near x*
-- statement:
--   Let $A \in \mathbb{R}^{n \times n}$ be a P-matrix, $f, \psi \in \mathbb{R}^n$, $c > 0$, and let $(y^*, \lambda^*)$ solve
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y - \psi)) = 0. \qquad (3.1)$$
--   Then there is $\rho > 0$ such that every run $(y^k, \lambda^k)_{k \ge 0}$ of the primal-dual active set algorithm (steps (ii)–(iii): $Ay^{k+1} + \lambda^{k+1} = f$, $y^{k+1} = \psi$ on $\mathcal{A}_k$, $\lambda^{k+1} = 0$ on $\mathcal{I}_k$) whose initial value satisfies $\|x^0 - x^*\| < \rho$, with $x^k = (y^k, \lambda^k)$ and $x^* = (y^*, \lambda^*)$, converges superlinearly to $x^*$: $x^k \to x^*$ and for every $\eta > 0$, eventually
--   $$\|x^{k+1} - x^*\| \le \eta\,\|x^k - x^*\|.$$
--
--   This is the local convergence theorem of the paper; by the equivalence of the active set step with the semismooth Newton step for (2.4), it is equally the local superlinear convergence of that semismooth Newton method.
--
--   **Formalization Note** The solution is a hypothesis; for a P-matrix it exists and is unique [BP], which is not restated here. $\rho$ depends on $A, f, \psi, c$ and the solution, but not on the run. The norm is the max of the sup norms of $y$ and $\lambda$; any norm on $\mathbb{R}^{2n}$ gives the same statement. The P-matrix property is the published definition `RobinsonSR.Schur.IsPMatrix`.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 7, Theorem 3.1

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.Local

open Filter Topology

/-- Theorem 3.1, p. 7: for a P-matrix `A`, `c > 0` and the solution `(y*, λ*)` of (3.1), the
primal-dual active set method converges superlinearly to `x* = (y*, λ*)`, provided that
`‖x⁰ - x*‖` is sufficiently small. The radius `ρ` depends on the data and the solution only,
not on the run. -/
theorem theorem_3_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : RobinsonSR.Schur.IsPMatrix A)
    (f ψ : Fin n → ℝ) (c : ℝ) (hc : 0 < c) (ystar lamstar : Fin n → ℝ)
    (hsol : IsSolution A f ψ c ystar lamstar) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y lam : ℕ → Fin n → ℝ, IsRun A f ψ c y lam →
      ‖(y 0, lam 0) - (ystar, lamstar)‖ < ρ →
      ConvergesSuperlinearly (fun k => (y k, lam k)) (ystar, lamstar) := by sorry

end PDASNewton.Local
