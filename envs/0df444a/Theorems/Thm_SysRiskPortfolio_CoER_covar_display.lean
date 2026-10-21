-- Prove2me | Theorems.Thm_SysRiskPortfolio_CoER_covar_display
-- name    : SysRiskPortfolio.CoER.covar_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:41.067687+00:00
-- url     : https://prove2.me/theorems/d02836a2-9679-4219-ab0e-0c91843c46f0
-- title:
--   CoVaR display, p. 28 — closed form conditional quantile
-- statement:
--   For a nondegenerate bivariate Gaussian portfolio and system with parameters $\mu_p,\mu_m,\sigma_p,\sigma_m,\rho$, and quantile levels $q_m,q_p\in(0,1)$, the conditional portfolio quantile at the system's VaR is
--   $$\operatorname{CoVaR}_{q_p}=\mu_p+\rho\sigma_p\Phi^{-1}(q_m)+\sigma_p\sqrt{1-\rho^2}\,\Phi^{-1}(q_p).$$
--   This is the paper's conditional risk threshold before the tail mean is calculated.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), p. 28, unnumbered CoVaR display

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_BivariateNormal

namespace SysRiskPortfolio.CoER

theorem covar_display (mup mum sp sm rho qm qp : ℝ) (hp : 0 < sp) (hm : 0 < sm) (hr : |rho| < 1) (hqm : 0 < qm ∧ qm < 1) (hqp : 0 < qp ∧ qp < 1) : CoVaR mup mum sp sm rho qm qp = mup + rho * sp * PhiInv qm + sp * Real.sqrt (1 - rho ^ 2) * PhiInv qp := by sorry

end SysRiskPortfolio.CoER
