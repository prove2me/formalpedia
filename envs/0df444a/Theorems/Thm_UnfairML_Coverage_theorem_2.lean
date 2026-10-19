-- Prove2me | Theorems.Thm_UnfairML_Coverage_theorem_2
-- name    : UnfairML.Coverage.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:38.111368+00:00
-- url     : https://prove2.me/theorems/4e1a0f41-c706-4d16-85ef-dcf4bccaec95
-- title:
--   Theorem 2, p. 23 — if αp/βp is low enough, the protected group's coverage rate is at least as high under equal treatment as under equal opportunity
-- statement:
--   Consider the bank of §3: two groups, a protected group $p$ and a regular group $r$, with expected profits $\alpha_p,\alpha_r$ and expected losses $\beta_p,\beta_r$ per group, learning rates $0<\gamma_p<\gamma_r$, effort $s\in[0,1/(2\gamma_r)]$, thresholds in $[0,1]$, profit (1) and learning cost $\tau(s)=ks/(1-\gamma_r s)$. Assume the standing assumptions of §3.1, case (1) ($\beta_p\le\alpha_p+\alpha_r$), and the cost range of p. 23:
--   $$k=\alpha_r\gamma_r+\sigma^2(\alpha_p\gamma_r-\beta_p\gamma_r+\beta_p\gamma_p),\qquad \sigma\in[\rho,1),\qquad \rho=\frac{1}{2-\gamma_p/\gamma_r}.$$
--
--   Let $(c^{ET},s^{ET})$ be any optimal decision of the bank under equal treatment ($c_p=c_r$), and $(c^{EO}_p,c^{EO}_r,s^{EO})$ any optimal decision under equal opportunity (equal coverage rates, constraint (6)). Write $\phi^{C}_p=\min\{(1-c^{C}_p)/(1-\gamma_p s^{C}),1\}$ for the protected group's coverage rate, the fraction of its good candidates accepted. If
--   $$\frac{\alpha_p}{\beta_p}\le 1-\frac{1-(2-\sigma)^2\sigma^2}{(1-\sigma^2)(2-\sigma)^2}\cdot\frac{\gamma_p}{\gamma_r},$$
--   then
--   $$\phi^{ET}_p\ \ge\ \phi^{EO}_p .$$
--
--   The equal-opportunity constraint is imposed to protect the protected group, but when lending to it is risky enough (low $\alpha_p/\beta_p$) the bank responds by learning less, and the protected group ends up with no larger a share of its good candidates accepted than under equal treatment.
--
--   **Formalization Note** The statement is about the optimal decisions of the joint problem (thresholds and effort) under profit (1), quantified over all optima. Effort ranges over the closed interval $[0,1/(2\gamma_r)]$ of Appendix A (at $\sigma=\rho$ the ET optimum is the endpoint), and $\alpha,\beta>0$ are added to the standing assumptions. The numerator printed "1−(2−σ)²)σ²" on the page is read as $1-(2-\sigma)^2\sigma^2$, as in (56) (labelled correction). The conclusion is $\ge$, as in the theorem; the last line of the proof says ">" but derives only $\ge$.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 23, Theorem 2 (proof pp. 44–45)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Theorem 2, p. 23: in case (1) with `k` in the range of p. 23, if
`αp/βp ≤ 1 − [(1 − (2 − σ)²σ²)/((1 − σ²)(2 − σ)²)] · γp/γr`, then the protected group's coverage
rate at the bank's optimal decision under equal treatment is at least its coverage rate at the
bank's optimal decision under equal opportunity: `φET_p ≥ φEO_p`. -/
theorem theorem_2 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ)
    (hcond : P.αp / P.βp ≤
      1 - (1 - (2 - σ) ^ 2 * σ ^ 2) / ((1 - σ ^ 2) * (2 - σ) ^ 2) * (P.γp / P.γr))
    (cET sET : ℝ) (hET : IsOptET P k cET sET)
    (cpEO crEO sEO : ℝ) (hEO : IsOptEO P k cpEO crEO sEO) :
    coverage P.γp cpEO sEO ≤ coverage P.γp cET sET := by sorry
end UnfairML.Coverage
