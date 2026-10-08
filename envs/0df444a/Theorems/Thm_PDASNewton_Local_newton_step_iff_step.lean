-- Prove2me | Theorems.Thm_PDASNewton_Local_newton_step_iff_step
-- name    : PDASNewton.Local.newton_step_iff_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:49.362981+00:00
-- url     : https://prove2.me/theorems/54c7a06e-e174-40b4-89ba-146029498867
-- title:
--   §2, pp. 4–5 — the semismooth Newton update based on (2.4) is the primal-dual active set step
-- statement:
--   Let $A \in \mathbb{R}^{n \times n}$, $f, \psi \in \mathbb{R}^n$ and $c > 0$. For iterates $x = (y, \lambda)$ and $x' = (y', \lambda')$,
--   $$G_F(x)\,(x' - x) = -F(x)$$
--   holds if and only if $(y', \lambda')$ follows $(y, \lambda)$ by one step of the primal-dual active set algorithm: $Ay' + \lambda' = f$, $y'_i = \psi_i$ on $\mathcal{A} = \{i : \lambda_i + c(y - \psi)_i > 0\}$ and $\lambda'_i = 0$ on $\mathcal{I} = \{i : \lambda_i + c(y - \psi)_i \le 0\}$.
--
--   This is the identification that makes "the primal-dual active set method or, equivalently, the semismooth Newton method" of Theorem 3.1 one statement.
--
--   **Formalization Note** $G_F$ uses $G_m$ with $\delta = 0$, as the paper does. No matrix hypothesis is needed.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, pp. 4–5, (2.4)–(2.6) and 'the semismooth Newton update based on (2.4) is equivalent to the primal-dual active set strategy'

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.Local

/-- §2, pp. 4–5: the semismooth Newton update based on (2.4),
`G_F(x^k)(x^{k+1} - x^k) = -F(x^k)`, is equivalent to one step (ii)–(iii) of the primal-dual
active set strategy. -/
theorem newton_step_iff_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ)
    (c : ℝ) (hc : 0 < c) (y lam y' lam' : Fin n → ℝ) :
    GF A ψ c (y, lam) ((y', lam') - (y, lam)) = -Fmap A f ψ c (y, lam) ↔
      IsStep A f ψ c y lam y' lam' := by sorry

end PDASNewton.Local
