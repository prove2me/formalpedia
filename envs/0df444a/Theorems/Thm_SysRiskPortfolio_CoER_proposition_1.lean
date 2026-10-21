-- Prove2me | Theorems.Thm_SysRiskPortfolio_CoER_proposition_1
-- name    : SysRiskPortfolio.CoER.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:05.430467+00:00
-- url     : https://prove2.me/theorems/e5096fc8-28b3-404d-9c10-3da3b0eff2e6
-- title:
--   Proposition 1, (2.4), p. 7 — vector form of CoER=
-- statement:
--   Under the paper's Gaussian and quantile assumptions, let $w$ be weights summing to one. With asset means $\mu$, covariance $\Sigma$, asset-system covariance $\sigma$, and system standard deviation $\sigma_m$, the co-expected return is
--   $$\operatorname{CoER}^{=}(w)=w^\top\mu+\frac{\Phi^{-1}(q_m)}{\sigma_m}w^\top\sigma-\frac{\phi(\Phi^{-1}(q_p))}{q_p}\sqrt{w^\top\Sigma w-\frac{(w^\top\sigma)^2}{\sigma_m^2}}.$$
--   This separates portfolio mean, system covariance and residual portfolio variance.
--
--   **Formalization Note** The joint covariance is positive definite to make the bivariate Gaussian and conditional density nondegenerate. This milestone covers (2.4); the separate derivative assertion (2.5) is outside this mission.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), p. 7, Proposition 1, (2.4)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_Portfolio

namespace SysRiskPortfolio.CoER

open Matrix

theorem proposition_1 {m : ℕ} (d : PortfolioData m) (hd : Standing d) (w : Fin (m + 1) → ℝ) (hw : ∑ i, w i = 1) : coerPort d w = w ⬝ᵥ d.mu + (PhiInv d.qm / d.sigM) * (w ⬝ᵥ d.sig) - (phi (PhiInv d.qp) / d.qp) * Real.sqrt (w ⬝ᵥ (d.Sig *ᵥ w) - (1 / d.sigM ^ 2) * (w ⬝ᵥ d.sig) ^ 2) := by sorry

end SysRiskPortfolio.CoER
