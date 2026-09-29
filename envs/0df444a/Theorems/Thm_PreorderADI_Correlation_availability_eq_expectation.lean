-- Prove2me | Theorems.Thm_PreorderADI_Correlation_availability_eq_expectation
-- name    : PreorderADI.Correlation.availability_eq_expectation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:50:49.459957+00:00
-- url     : https://prove2.me/theorems/06ef1338-31ef-41d2-9afe-795452a49564
-- title:
--   §4 (3) — the availability belief ξ = 𝔼[Pr(X̃_L(X)/2 < Q(X))] = 𝔼[Φ((λ_L + ρX)/√(1 − ρ²) + 2z_L)]
-- statement:
--   Fix the model parameters under the standing assumptions and $\rho \in [0,1)$. For every realization $x$ of the standard normal variable $X$, the probability that half the updated low-type demand falls short of the order quantity $Q(x) = \tilde\mu_L(x) + z_L\tilde\sigma_L$ is
--
--   $$
--   \Pr\Big(\frac{\tilde X_L(x)}{2} < Q(x)\Big) = \Phi\Big(\frac{\lambda_L + \rho x}{\sqrt{1-\rho^2}} + 2z_L\Big),
--   $$
--
--   where $\lambda_L = \mu_L/\sigma_L$. Consequently the consumers' belief of product availability (3) is
--
--   $$
--   \xi = \mathbb E\Big[\Pr\Big(\frac{\tilde X_L(X)}{2} < Q(X)\Big)\Big] = \mathbb E\Big[\Phi\Big(\frac{\lambda_L + \rho X}{\sqrt{1-\rho^2}} + 2z_L\Big)\Big].
--   $$
--
--   The factor $1/2$ is the rationing belief $\theta = 1/2$: a waiting high type believes half of the remaining consumers are served before her. The identity turns the availability into an expectation of a normal distribution function, which is the form in which its dependence on $\rho$ is analysed.
--
--   **Formalization Note** $\xi$ is defined as the first expression of (3); this theorem is the paper's "second equality". The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 61, §4, (3)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem availability_eq_expectation (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1) :
    (∀ x : ℝ, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x} =
      stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL)) ∧
    availability P ρ =
      ∫ x, stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL)
        ∂(gaussianReal 0 1) := by sorry

end PreorderADI.Correlation
