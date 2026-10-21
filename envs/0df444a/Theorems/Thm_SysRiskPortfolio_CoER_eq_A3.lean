-- Prove2me | Theorems.Thm_SysRiskPortfolio_CoER_eq_A3
-- name    : SysRiskPortfolio.CoER.eq_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:30.888224+00:00
-- url     : https://prove2.me/theorems/d8bd8f33-4883-47bb-bd7d-26271e53dc31
-- title:
--   (A.3), p. 27 — conditional bivariate Gaussian law
-- statement:
--   Let $(X,Y)$ be bivariate Gaussian with means $\mu_x,\mu_y$, positive standard deviations $\sigma_x,\sigma_y$, and correlation $|\rho|<1$. For every real $y$, the density-ratio conditional law of $X$ given $Y=y$ is
--   $$N\!\left(\mu_x+\rho\sigma_x\frac{y-\mu_y}{\sigma_y},\ \sigma_x^2(1-\rho^2)\right).$$
--   This identifies the conditional distribution behind CoVaR and CoER=.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), p. 27, (A.3)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_BivariateNormal

namespace SysRiskPortfolio.CoER

theorem eq_A3 (mux muy sx sy rho y : ℝ) (hx : 0 < sx) (hy : 0 < sy) (hr : |rho| < 1) : condLaw mux muy sx sy rho y = ProbabilityTheory.gaussianReal (mux + rho * sx * (y - muy) / sy) ⟨sx ^ 2 * (1 - rho ^ 2), mul_nonneg (sq_nonneg sx) (by have h := abs_lt.mp hr; nlinarith)⟩ := by sorry

end SysRiskPortfolio.CoER
