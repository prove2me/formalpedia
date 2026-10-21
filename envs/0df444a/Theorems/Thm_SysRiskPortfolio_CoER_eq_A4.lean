-- Prove2me | Theorems.Thm_SysRiskPortfolio_CoER_eq_A4
-- name    : SysRiskPortfolio.CoER.eq_A4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:34.267305+00:00
-- url     : https://prove2.me/theorems/3a8a9f82-16d1-4583-bce4-f2ee495613a2
-- title:
--   (A.4), p. 28 — Gaussian co-expected return
-- statement:
--   For the same nondegenerate bivariate Gaussian model and $q_m,q_p\in(0,1)$, the conditional mean of portfolio returns below CoVaR is
--   $$\operatorname{CoER}^{=}=\mu_p+\sigma_p\left(\rho\Phi^{-1}(q_m)-\frac{\sqrt{1-\rho^2}}{q_p}\phi(\Phi^{-1}(q_p))\right).$$
--   This is the scalar closed form from which the portfolio expression follows.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), p. 28, (A.4)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_BivariateNormal

namespace SysRiskPortfolio.CoER

theorem eq_A4 (mup mum sp sm rho qm qp : ℝ) (hp : 0 < sp) (hm : 0 < sm) (hr : |rho| < 1) (hqm : 0 < qm ∧ qm < 1) (hqp : 0 < qp ∧ qp < 1) : CoER mup mum sp sm rho qm qp = mup + sp * (rho * PhiInv qm - (1 / qp) * Real.sqrt (1 - rho ^ 2) * phi (PhiInv qp)) := by sorry

end SysRiskPortfolio.CoER
