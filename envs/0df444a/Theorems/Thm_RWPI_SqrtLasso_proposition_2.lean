-- Prove2me | Theorems.Thm_RWPI_SqrtLasso_proposition_2
-- name    : RWPI.SqrtLasso.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:09:01.444752+00:00
-- url     : https://prove2.me/theorems/5e29a349-c73c-4065-a794-2b9653703e62
-- title:
--   Proposition 2 — DR linear regression with the squared $\ell_q$ cost: worst-case square loss $=(\sqrt{\mathrm{MSE}_n(\beta)}+\sqrt\delta\|\bar\beta\|_p)^2$
-- statement:
--   Fix $q\in(1,\infty]$ and let $p$ satisfy $1/p+1/q = 1$. Let $(X_1,Y_1),\dots,(X_n,Y_n)\in\mathbb R^d\times\mathbb R$, $n\ge1$, be training data with empirical distribution $P_n$, and let $\delta\ge0$. Take the square loss $l(x,y;\beta) = (y-\beta^Tx)^2$ and the cost $c((x,y),(u,v)) = \|(x,y)-(u,v)\|_q^2$ on $\mathbb R^{d+1}$, with optimal transport cost $D_c$ as in (7). Write $\bar\beta = (-\beta,1)$ and $\mathrm{MSE}_n(\beta) = \frac1n\sum_{i=1}^n (Y_i-\beta^TX_i)^2$. Then:
--
--   1. for every $\beta\in\mathbb R^d$,
--   $$
--   \sup_{P:\ D_c(P,P_n)\le\delta}\mathbb E_P\big[(Y-\beta^TX)^2\big] = \Big(\sqrt{\mathrm{MSE}_n(\beta)} + \sqrt\delta\,\|\bar\beta\|_p\Big)^2 ;
--   $$
--   2. consequently (Eq. (13)),
--   $$
--   \inf_{\beta\in\mathbb R^d}\ \sup_{P:\ D_c(P,P_n)\le\delta}\mathbb E_P\big[(Y-\beta^TX)^2\big] = \inf_{\beta\in\mathbb R^d}\Big(\sqrt{\mathrm{MSE}_n(\beta)} + \sqrt\delta\,\|\bar\beta\|_p\Big)^2 .
--   $$
--
--   The distributionally robust least-squares problem with an $\ell_q$-transport ball is a regularized regression whose penalty is $\|\bar\beta\|_p$, which also charges the intercept-like coordinate $1$. Theorem 1 removes that coordinate by forbidding transport of the response.
--
--   **Formalization Note** Item 1 is the display that concludes the paper's proof (p. 29); item 2 is the printed statement (13). The page's statement does not mention $\delta\ge0$; it is the radius of the ball. The data space is $(\text{Fin } d\to\mathbb R)\times\mathbb R$, and the cost is the $\ell_q$ norm of the stacked vector in $\mathbb R^{d+1}$. Both sides are compared in $[0,\infty]$; the right side is a real number embedded by `ENNReal.ofReal`.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Proposition 2, Eq. (13); pointwise form from App. A.1, p. 29 (display after (29))

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_RWPI_SqrtLasso_squareLoss
import Definitions.Def_RWPI_SqrtLasso_MSE
import Definitions.Def_RWPI_SqrtLasso_lqSqCost

open MeasureTheory

namespace RWPI.SqrtLasso

/-- Proposition 2 (p. 10), with the pointwise identity its proof establishes (p. 29). Fix
`q ∈ (1, ∞]` and `p` with `1/p + 1/q = 1`. For the square loss and the cost
`c((x, y), (u, v)) = ‖(x, y) − (u, v)‖_q²` on `ℝ^{d+1}`, and every `δ ≥ 0`:
(1) for every `β`, `sup_{P : D_c(P, P_n) ≤ δ} E_P[(Y − βᵀX)²] = (√MSE_n(β) + √δ ‖β̄‖_p)²`;
(2) (13): the infima over `β ∈ ℝ^d` of both sides agree. -/
theorem proposition_2 {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ β : Fin d → ℝ,
      worstCase (lqSqCost q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β) =
        ENNReal.ofReal
          ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p (betaBar β)‖) ^ 2)) ∧
    (⨅ β : Fin d → ℝ, worstCase (lqSqCost q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β)) =
      ⨅ β : Fin d → ℝ, ENNReal.ofReal
          ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p (betaBar β)‖) ^ 2) := by sorry

end RWPI.SqrtLasso
