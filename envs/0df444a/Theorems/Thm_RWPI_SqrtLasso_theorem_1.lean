-- Prove2me | Theorems.Thm_RWPI_SqrtLasso_theorem_1
-- name    : RWPI.SqrtLasso.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:09:24.748689+00:00
-- url     : https://prove2.me/theorems/f08cd6ee-e954-4e29-8416-578722da4400
-- title:
--   Theorem 1 — square-root LASSO is Wasserstein DRO: worst-case squared loss under $N_q^2$ equals $(\sqrt{\mathrm{MSE}_n(\beta)}+\sqrt\delta\|\beta\|_p)^2$
-- statement:
--   Fix $q\in(1,\infty]$ and let $p$ satisfy $1/p+1/q = 1$. Let $(X_1,Y_1),\dots,(X_n,Y_n)\in\mathbb R^d\times\mathbb R$, $n\ge1$, be training data with empirical distribution $P_n$, and let $\delta\ge0$. Consider the square loss $l(x,y;\beta) = (y-\beta^Tx)^2$ and the optimal transport cost $D_c$ of (7) with
--
--   $$
--   c\big((x,y),(u,v)\big) = N_q\big((x,y),(u,v)\big)^2, \qquad N_q\big((x,y),(u,v)\big) = \begin{cases}\|x-u\|_q, & y = v,\\ +\infty, & y\ne v.\end{cases}
--   $$
--
--   Let $\mathrm{MSE}_n(\beta) = \frac1n\sum_{i=1}^n (Y_i-\beta^TX_i)^2$. Then:
--
--   1. for every $\beta\in\mathbb R^d$,
--   $$
--   \sup_{P:\ D_c(P,P_n)\le\delta}\mathbb E_P\big[(Y-\beta^TX)^2\big] = \Big(\sqrt{\mathrm{MSE}_n(\beta)} + \sqrt\delta\,\|\beta\|_p\Big)^2 ;
--   $$
--   2. consequently,
--   $$
--   \inf_{\beta\in\mathbb R^d}\ \sup_{P:\ D_c(P,P_n)\le\delta}\mathbb E_P\big[(Y-\beta^TX)^2\big] = \inf_{\beta\in\mathbb R^d}\Big(\sqrt{\mathrm{MSE}_n(\beta)} + \sqrt\delta\,\|\beta\|_p\Big)^2 .
--   $$
--
--   The right side of item 2 is the $\ell_p$-penalized square-root least-squares problem: for $q = \infty$ ($p = 1$) its minimizers are those of the square-root LASSO $\sqrt{\mathrm{MSE}_n(\beta)}+\sqrt\delta\|\beta\|_1$. The theorem therefore identifies these estimators exactly as distributionally robust least-squares estimators, with the radius $\delta$ of the transport ball playing the role of the squared regularization parameter.
--
--   **Formalization Note** Item 2 is the printed statement; item 1 is the identity the paper's proof establishes for each $\beta$ (App. A.1, p. 29). The page does not state the range of $q$; Proposition 2 fixes $q\in(1,\infty]$ and the paper calls Theorem 1 "essentially the same", so that range is used. $\delta\ge0$ is the radius of the ball. Expectations are lower Lebesgue integrals in $[0,\infty]$, the supremum is over all probability measures on $(\text{Fin } d\to\mathbb R)\times\mathbb R$ within transport cost $\delta$ of $P_n$, couplings fix both marginals, and the right side is a real number embedded by `ENNReal.ofReal`. $\|\beta\|_p$ is the `PiLp p` norm.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 11, Theorem 1 (pointwise form from App. A.1, p. 29)

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_RWPI_SqrtLasso_squareLoss
import Definitions.Def_RWPI_SqrtLasso_MSE
import Definitions.Def_RWPI_SqrtLasso_Nq

open MeasureTheory

namespace RWPI.SqrtLasso

/-- Theorem 1 (Blanchet, Kang & Murthy, p. 11), with the pointwise identity its proof establishes.
For the square loss `l(x, y; β) = (y − βᵀx)²`, the cost `c = N_q^ρ` with `ρ = 2`
(`N_q((x, y), (u, v)) = ‖x − u‖_q` if `y = v`, `+∞` otherwise), `q ∈ (1, ∞]`, `1/p + 1/q = 1`, the
empirical distribution `P_n` of the data `(X_i, Y_i)` and every `δ ≥ 0`:
(1) for every `β`, `sup_{P : D_c(P, P_n) ≤ δ} E_P[(Y − βᵀX)²] = (√MSE_n(β) + √δ ‖β‖_p)²`;
(2) `inf_β sup_{P : D_c(P, P_n) ≤ δ} E_P[(Y − βᵀX)²] = inf_β (√MSE_n(β) + √δ ‖β‖_p)²`. -/
theorem theorem_1 {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ β : Fin d → ℝ,
      worstCase (fun z w => Nq q z w ^ 2) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β) =
        ENNReal.ofReal ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2)) ∧
    (⨅ β : Fin d → ℝ, worstCase (fun z w => Nq q z w ^ 2) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β)) =
      ⨅ β : Fin d → ℝ, ENNReal.ofReal
          ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2) := by sorry

end RWPI.SqrtLasso
