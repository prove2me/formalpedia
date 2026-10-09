-- Prove2me | Theorems.Thm_StatComplexityDM_LinearLB_rad_hellinger_bounds
-- name    : StatComplexityDM.LinearLB.rad_hellinger_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:24.730378+00:00
-- url     : https://prove2.me/theorems/e0ad4c9f-cf71-43d3-b347-e8f53868700d
-- title:
--   Lemma A.8, p. 71 — D²_H(Rad(μ₁), Rad(μ₂)) ≤ ((μ₁−μ₂)²/2)(1/(2+μ₁+μ₂) + 1/(2−μ₁−μ₂)); ≤ (μ₁−μ₂)² on [−½, ½]; D²_H(Rad(μ), Rad(0)) ≤ ¾μ²
-- statement:
--   Let $\mathrm{Rad}(\mu)$ be the Rademacher distribution on $\{-1,+1\}$ with mean $\mu \in [-1,1]$, i.e. $\mathrm{Rad}(\mu)(+1) = (1+\mu)/2$ and $\mathrm{Rad}(\mu)(-1) = (1-\mu)/2$, and let $D^2_{\mathrm{H}}(P,Q) = \sum_y (\sqrt{P(y)} - \sqrt{Q(y)})^2$ be the squared Hellinger distance. Then:
--
--   1. For all $\mu_1, \mu_2 \in [-1, +1]$,
--   $$
--   D^2_{\mathrm{H}}\bigl(\mathrm{Rad}(\mu_1), \mathrm{Rad}(\mu_2)\bigr) \le \frac{(\mu_1 - \mu_2)^2}{2} \left( \frac{1}{2 + \mu_1 + \mu_2} + \frac{1}{2 - \mu_1 - \mu_2} \right).
--   $$
--   2. For all $\mu_1, \mu_2 \in [-\tfrac12, +\tfrac12]$, $\ D^2_{\mathrm{H}}\bigl(\mathrm{Rad}(\mu_1), \mathrm{Rad}(\mu_2)\bigr) \le (\mu_1 - \mu_2)^2$.
--   3. For all $\mu \in [-1, +1]$, $\ D^2_{\mathrm{H}}\bigl(\mathrm{Rad}(\mu), \mathrm{Rad}(0)\bigr) \le \tfrac34 \mu^2$.
--
--   The third bound is the information property of the hard family in the linear bandit lower bound (Proposition 6.2): a model whose mean differs from that of $\mathrm{Rad}(0)$ by $\mu$ is at squared Hellinger distance $O(\mu^2)$ from it.
--
--   **Formalization Note** In the first bound, a denominator $2 \pm (\mu_1 + \mu_2)$ vanishes only when $\mu_1 = \mu_2 = \mp 1$; there both sides are $0$ (Lean's convention $1/0 = 0$ gives right-hand side $0 \cdot \tfrac14 = 0$), so the literal division form is stated. Outcomes are encoded on `Bool`.
-- source:
--   arXiv:2112.13487v3, Lemma A.8, p. 71

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LinearLB_Setting

namespace StatComplexityDM.LinearLB

open FoundationsRL.GeneralDM

/-- Lemma A.8 (arXiv:2112.13487v3, p. 71): squared Hellinger distance between Rademacher
distributions, all three displays. -/
theorem rad_hellinger_bounds :
    (∀ μ₁ μ₂ : ℝ, μ₁ ∈ Set.Icc (-1 : ℝ) 1 → μ₂ ∈ Set.Icc (-1 : ℝ) 1 →
      hellingerSq (rad μ₁) (rad μ₂) ≤
        (μ₁ - μ₂) ^ 2 / 2 * (1 / (2 + μ₁ + μ₂) + 1 / (2 - μ₁ - μ₂))) ∧
    (∀ μ₁ μ₂ : ℝ, μ₁ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) → μ₂ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) →
      hellingerSq (rad μ₁) (rad μ₂) ≤ (μ₁ - μ₂) ^ 2) ∧
    (∀ μ : ℝ, μ ∈ Set.Icc (-1 : ℝ) 1 →
      hellingerSq (rad μ) (rad 0) ≤ 3 / 4 * μ ^ 2) := by sorry

end StatComplexityDM.LinearLB
