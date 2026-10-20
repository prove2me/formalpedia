-- Prove2me | Theorems.Thm_PrivacyQueue_Control_bracket_positive
-- name    : PrivacyQueue.Control.bracket_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:09.783321+00:00
-- url     : https://prove2.me/theorems/6ccf2e9d-e7b2-4a52-8820-3da342543605
-- title:
--   Proof of Lemma 4 — denominator bracket stays positive
-- statement:
--   Write $A=(\mu-\alpha\lambda)(\alpha^2\sigma^2+(\alpha-1)^2)$. In the noncritical parameter regime, the proof of Lemma 4 gives the endpoint identities
--
--   $$A-\alpha(1-\alpha)\Gamma(0)=\mu(1-\alpha(1+\sigma))^2\frac{\sigma\mu-(1-\alpha)\lambda-\sigma\alpha\lambda}{\sigma\mu-(1-\alpha)\lambda},$$
--   $$A-\alpha(1-\alpha)\Gamma(1)=(\mu-\alpha\lambda)(1-\alpha(1+\sigma))^2.$$
--
--   Moreover, $A-\alpha(1-\alpha)\Gamma(\gamma)>0$ for every $\gamma\in[0,1]$. This guarantees the sign of the second fraction in the closed form of total customer surplus.
--
--   **Formalization Note** The auxiliary item excludes $\alpha(1+\sigma)=1$, at which both displayed endpoint expressions vanish.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), Online Supplement p. 2 (PDF 49), proof of Lemma 4, final displayed endpoint identities

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

namespace PrivacyQueue.Control

/-- Proof of Lemma 4, Online Supplement p. 2: the denominator bracket is positive. -/
theorem bracket_positive (P : Params) (hS : P.Standing)
    (hCritical : P.α * (1 + P.σ) ≠ 1) :
    (P.mu - P.α * P.lam) * (P.α ^ 2 * P.σ ^ 2 + (P.α - 1) ^ 2) -
        P.α * (1 - P.α) * Gam P 0 =
      P.mu * (1 - P.α * (1 + P.σ)) ^ 2 *
        (P.σ * P.mu - (1 - P.α) * P.lam - P.σ * P.α * P.lam) /
        (P.σ * P.mu - (1 - P.α) * P.lam) ∧
    (P.mu - P.α * P.lam) * (P.α ^ 2 * P.σ ^ 2 + (P.α - 1) ^ 2) -
        P.α * (1 - P.α) * Gam P 1 =
      (P.mu - P.α * P.lam) * (1 - P.α * (1 + P.σ)) ^ 2 ∧
    ∀ γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 →
      0 < (P.mu - P.α * P.lam) *
        (P.α ^ 2 * P.σ ^ 2 + (P.α - 1) ^ 2) -
        P.α * (1 - P.α) * Gam P γ := by sorry

end PrivacyQueue.Control
