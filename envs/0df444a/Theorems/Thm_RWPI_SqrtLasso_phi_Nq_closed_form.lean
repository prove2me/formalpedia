-- Prove2me | Theorems.Thm_RWPI_SqrtLasso_phi_Nq_closed_form
-- name    : RWPI.SqrtLasso.phi_Nq_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:46:40.936486+00:00
-- url     : https://prove2.me/theorems/4449c548-688b-455a-9937-9e7ceca6d4f7
-- title:
--   Outline of the proof of Theorem 1 — $\varphi_\gamma$ for the square loss and the cost $N_q^2$ (corrected at $\gamma = \|\beta\|_p^2$)
-- statement:
--   Fix $q\in(1,\infty]$ and let $p$ satisfy $1/p+1/q = 1$. Let $\beta\in\mathbb R^d$ and $(x,y)\in\mathbb R^d\times\mathbb R$, and write $a = y-\beta^Tx$. For the square loss and the cost $N_q^2$ of (14), let
--
--   $$
--   \varphi_\gamma(x,y;\beta) = \sup_{x'\in\mathbb R^d,\ y'\in\mathbb R}\Big\{ (y'-\beta^Tx')^2 - \gamma\,N_q\big((x',y'),(x,y)\big)^2 \Big\},
--   $$
--
--   where points with $y'\ne y$ (infinite cost) do not contribute. Then for every $\gamma\ge0$
--
--   $$
--   \varphi_\gamma(x,y;\beta) = \begin{cases} \dfrac{\gamma}{\gamma-\|\beta\|_p^2}\,a^2, & \text{if } \gamma>\|\beta\|_p^2,\\[2mm] a^2, & \text{if } \gamma = \|\beta\|_p^2 \text{ and } (a = 0 \text{ or } \beta = 0),\\[1mm] +\infty, & \text{otherwise.}\end{cases}
--   $$
--
--   With this formula and Proposition 1, the worst-case square loss of Theorem 1 becomes a one-dimensional minimization over $\gamma$.
--
--   **Correction of the printed statement.** The page gives $+\infty$ for every $\gamma\le\|\beta\|_p^2$ (and writes $\lambda$ for $\gamma$ and $\varphi_\gamma(x,y;\beta)$ for $\varphi_\gamma(X_i,Y_i;\beta)$). At $\gamma = \|\beta\|_p^2$ the supremum is finite when $a = 0$ (value $0$) or when $\beta = 0$ (then $\gamma = 0$ and the value is $y^2$). The correction does not affect Theorem 1.
--
--   **Formalization Note** $\varphi_\gamma$ is the mission's `phi` with the cost $N_q^2$; the convention that infinite-cost points never contribute holds for every $\gamma\ge0$, including $\gamma = 0$. Values are in $[0,\infty]$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 29, App. A.1, outline of a proof of Theorem 1, last display

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_phi
import Definitions.Def_RWPI_SqrtLasso_squareLoss
import Definitions.Def_RWPI_SqrtLasso_Nq

namespace RWPI.SqrtLasso

/-- Outline of the proof of Theorem 1, last display (App. A.1, p. 29), corrected at the boundary:
`φ_γ` for the square loss and the cost `N_q²`. With `a = y − βᵀx`, `1/p + 1/q = 1` and `γ ≥ 0`:
`φ_γ((x, y); β) = γ/(γ − ‖β‖_p²) · a²` if `γ > ‖β‖_p²`; `a²` if `γ = ‖β‖_p²` and (`a = 0` or
`β = 0`); `+∞` otherwise. (The page prints `+∞` for all `γ ≤ ‖β‖_p²`.) -/
theorem phi_Nq_closed_form {d : ℕ} (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    phi (fun u w => Nq q u w ^ 2) (squareLoss β) γ z =
      if ‖WithLp.toLp p β‖ ^ 2 < γ then
        ENNReal.ofReal (γ / (γ - ‖WithLp.toLp p β‖ ^ 2) * (z.2 - ∑ j, β j * z.1 j) ^ 2)
      else if γ = ‖WithLp.toLp p β‖ ^ 2 ∧ (z.2 - ∑ j, β j * z.1 j = 0 ∨ β = 0) then
        ENNReal.ofReal ((z.2 - ∑ j, β j * z.1 j) ^ 2)
      else ⊤ := by sorry

end RWPI.SqrtLasso
