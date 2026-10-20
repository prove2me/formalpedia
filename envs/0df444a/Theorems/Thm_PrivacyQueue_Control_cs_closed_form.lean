-- Prove2me | Theorems.Thm_PrivacyQueue_Control_cs_closed_form
-- name    : PrivacyQueue.Control.cs_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:02.513181+00:00
-- url     : https://prove2.me/theorems/9ff3227c-00ba-490b-aa2b-799e84798ef8
-- title:
--   Proof of Lemma 4 — closed form of total customer surplus
-- statement:
--   For the stable queue with $\gamma\in[0,1]$, the proof of Lemma 4 rewrites total customer surplus as
--
--   $$CS(\gamma)=\lambda R-\lambda c\left(\frac{\sigma(\sigma-1)\mu+\lambda(\alpha\sigma^3-\alpha\sigma^2+\alpha\sigma+1-\alpha)}{\sigma\lambda(\sigma\mu-\lambda(\alpha\sigma+1-\alpha))}+\frac{(1-\sigma)(\mu-\lambda\alpha(1-\sigma))(1-\alpha(1+\sigma))^2}{\sigma\lambda\bigl((\mu-\alpha\lambda)(\alpha^2\sigma^2+(\alpha-1)^2)-\alpha(1-\alpha)\Gamma(\gamma)\bigr)}\right),$$
--
--   where $\Gamma(\gamma)=\gamma\lambda(1-\alpha(1+\sigma))+(\sigma\mu-(1-\alpha)\lambda)+\frac{\sigma^2(\mu-\alpha\lambda)^2}{\gamma\lambda(1-\alpha-\alpha\sigma)+(\sigma\mu-(1-\alpha)\lambda)}$.
--
--   This is the rational form analyzed to obtain the monotonicity of $CS$.
--
--   **Formalization Note** The source's second fraction is $0/0$ when $\alpha(1+\sigma)=1$, so that parameter value is excluded from this auxiliary identity. Lemma 4 itself has no such exclusion.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), Online Supplement p. 2 (PDF 49), proof of Lemma 4, displayed CS and Γ expressions

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

namespace PrivacyQueue.Control

/-- Proof of Lemma 4, Online Supplement p. 2: closed form of surplus. -/
theorem cs_closed_form (P : Params) (hS : P.Standing)
    (hCritical : P.α * (1 + P.σ) ≠ 1) (γ : ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    CS P γ = P.lam * P.R - P.lam * P.c *
      ((P.σ * (P.σ - 1) * P.mu +
          P.lam * (P.α * P.σ ^ 3 - P.α * P.σ ^ 2 +
            P.α * P.σ + 1 - P.α)) /
          (P.σ * P.lam *
            (P.σ * P.mu - P.lam * (P.α * P.σ + 1 - P.α))) +
       ((1 - P.σ) * (P.mu - P.lam * P.α * (1 - P.σ)) *
          (1 - P.α * (1 + P.σ)) ^ 2) /
          (P.σ * P.lam *
            ((P.mu - P.α * P.lam) *
                (P.α ^ 2 * P.σ ^ 2 + (P.α - 1) ^ 2) -
              P.α * (1 - P.α) * Gam P γ))) := by sorry

end PrivacyQueue.Control
