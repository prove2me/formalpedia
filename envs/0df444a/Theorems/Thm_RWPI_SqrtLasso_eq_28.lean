-- Prove2me | Theorems.Thm_RWPI_SqrtLasso_eq_28
-- name    : RWPI.SqrtLasso.eq_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:46:16.171913+00:00
-- url     : https://prove2.me/theorems/6bcf2dc4-94fd-4f9e-8dff-d21f52c86221
-- title:
--   (28) — closed form of $\varphi_\gamma$ for the square loss and the squared $\ell_q$ cost (corrected at $\gamma = \|\bar\beta\|_p^2$)
-- statement:
--   Fix $q\in(1,\infty]$ and let $p$ satisfy $1/p+1/q = 1$. Let $\beta\in\mathbb R^d$, $\bar\beta = (-\beta,1)$, and let $\bar x = (x,y)\in\mathbb R^{d+1}$ be a point. For the square loss $l(\bar u;\beta) = (\bar\beta^T\bar u)^2$ and the cost $c(\bar u,\bar x) = \|\bar u-\bar x\|_q^2$, define $\varphi_\gamma(\bar x;\beta) = \sup_{\bar u\in\mathbb R^{d+1}}\{(\bar\beta^T\bar u)^2 - \gamma\|\bar x-\bar u\|_q^2\}$. Then for every $\gamma\ge0$
--
--   $$
--   \varphi_\gamma(\bar x;\beta) = \begin{cases} \big(\bar\beta^T\bar x\big)^2\,\dfrac{\gamma}{\gamma-\|\bar\beta\|_p^2}, & \text{if } \gamma > \|\bar\beta\|_p^2,\\[2mm] 0, & \text{if } \gamma = \|\bar\beta\|_p^2 \text{ and } \bar\beta^T\bar x = 0,\\[1mm] +\infty, & \text{otherwise.}\end{cases}
--   $$
--
--   This is the inner supremum of Proposition 1's dual in the setting of Proposition 2; with it the dual becomes a one-dimensional problem in $\gamma$.
--
--   **Correction of the printed statement.** The page gives $+\infty$ for every $\gamma\le\|\bar\beta\|_p^2$. At $\gamma = \|\bar\beta\|_p^2$ the bracket is at most $(\bar\beta^T\bar x)^2 + 2(\bar\beta^T\bar x)(\bar\beta^T\Delta)$ with $\Delta = \bar u-\bar x$, which is bounded (by $0$) when $\bar\beta^T\bar x = 0$. The correction does not affect Proposition 2.
--
--   **Formalization Note** The point is a pair $z = (x,y)$ and $\bar x$ is `stack z`; $\|\cdot\|_p$, $\|\cdot\|_q$ are the norms of `PiLp`. The value is in $[0,\infty]$; $\varphi_\gamma$ is the mission's `phi` with the cost `lqSqCost q`.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 29, App. A.1, proof of Proposition 2, Eq. (28) (derivation from p. 28)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_phi
import Definitions.Def_RWPI_SqrtLasso_squareLoss
import Definitions.Def_RWPI_SqrtLasso_lqSqCost

namespace RWPI.SqrtLasso

/-- Eq. (28) (App. A.1, proof of Proposition 2, p. 29), corrected at the boundary: the closed form
of `φ_γ` for the square loss and the squared `ℓ_q` cost on `ℝ^{d+1}`. With `x̄ = (x, y)`,
`β̄ = (−β, 1)` and `1/p + 1/q = 1`, for `γ ≥ 0`:
`φ_γ(x̄; β) = (β̄ᵀx̄)² γ / (γ − ‖β̄‖_p²)` if `γ > ‖β̄‖_p²`; `0` if `γ = ‖β̄‖_p²` and `β̄ᵀx̄ = 0`;
`+∞` otherwise. (The page prints `+∞` for all `γ ≤ ‖β̄‖_p²`, which is wrong at the single case
`γ = ‖β̄‖_p²`, `β̄ᵀx̄ = 0`.) -/
theorem eq_28 {d : ℕ} (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    phi (lqSqCost q) (squareLoss β) γ z =
      if ‖WithLp.toLp p (betaBar β)‖ ^ 2 < γ then
        ENNReal.ofReal ((∑ j, betaBar β j * stack z j) ^ 2 * γ /
          (γ - ‖WithLp.toLp p (betaBar β)‖ ^ 2))
      else if γ = ‖WithLp.toLp p (betaBar β)‖ ^ 2 ∧ ∑ j, betaBar β j * stack z j = 0 then 0
      else ⊤ := by sorry

end RWPI.SqrtLasso
