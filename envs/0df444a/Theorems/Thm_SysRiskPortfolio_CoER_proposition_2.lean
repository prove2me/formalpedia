-- Prove2me | Theorems.Thm_SysRiskPortfolio_CoER_proposition_2
-- name    : SysRiskPortfolio.CoER.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:27.329602+00:00
-- url     : https://prove2.me/theorems/77876b99-96e4-4a10-9fb6-93dc1ba5a5b6
-- title:
--   Proposition 2, p. 9 — unique closed-form maximizer of CoER=
-- statement:
--   Consider $n\ge2$ risky assets and the paper's Gaussian model with stressed quantile levels $q_m,q_p\in(0,1/2)$. Let $\widehat\mu,\widehat\Sigma,\lambda,\Delta,Q$ be defined by (A.6)–(A.7), and let $w^*$ be the portfolio printed in Proposition 2. If
--   $$\lambda>\sqrt{\Delta^\top Q^{-1}\Delta},$$
--   then $\mathbf1^\top w^*=1$, $\operatorname{CoER}^{=}(w)\le\operatorname{CoER}^{=}(w^*)$ for every portfolio with $\mathbf1^\top w=1$, and equality holds only when $w=w^*$.
--
--   This is the paper's closed-form solution to the system-at-VaR portfolio selection problem.
--
--   **Formalization Note** The joint asset-system covariance is assumed positive definite, making the Gaussian conditional law, Schur complement, and inverses nondegenerate. CoER= remains defined by the conditional density and tail integral, rather than by the closed form proved in the milestones.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), p. 9, Proposition 2, (2.6); p. 29, (A.7)–(A.8)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_Portfolio

namespace SysRiskPortfolio.CoER

open Matrix

theorem proposition_2 {m : ℕ} (d : PortfolioData m) (hd : Standing d) (hlam : Real.sqrt (Del (optimData d) ⬝ᵥ ((Qm (optimData d))⁻¹ *ᵥ Del (optimData d))) < (optimData d).lam) : (∑ i, wStar (optimData d) i) = 1 ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → coerPort d w ≤ coerPort d (wStar (optimData d))) ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → coerPort d w = coerPort d (wStar (optimData d)) → w = wStar (optimData d)) := by sorry

end SysRiskPortfolio.CoER
