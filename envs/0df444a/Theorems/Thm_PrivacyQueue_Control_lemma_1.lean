-- Prove2me | Theorems.Thm_PrivacyQueue_Control_lemma_1
-- name    : PrivacyQueue.Control.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:04.645957+00:00
-- url     : https://prove2.me/theorems/7aff839d-c1d6-43dd-bb92-9de9bbe299b6
-- title:
--   Lemma 1 — closed forms of disclosure and withholding utility
-- statement:
--   Fix the paper's stable two-type queue, and let $\gamma\in[0,1]$ be the population disclosure probability. For an infinitesimal customer, the expected utilities of disclosing and withholding are
--
--   $$U_d(\gamma,\lambda)=R-c\left(\frac{\alpha}{\mu-\alpha\lambda\gamma}+\frac{\sigma(1-\alpha)(\mu+\lambda\alpha(\sigma-1))}{(\sigma\mu-\lambda(1+\alpha(\sigma-1)))(\sigma\mu-\lambda(\alpha\sigma+(1-\gamma)(1-\alpha)))}\right),$$
--   $$U_w(\gamma,\lambda)=R-c\frac{\sigma(1+\alpha(\sigma-1))\mu-\lambda\alpha(\alpha-1)(\sigma-1)(\sigma+\gamma-1)}{\sigma(\mu-\lambda\alpha\gamma)(\sigma\mu-\lambda(\alpha\sigma+(1-\gamma)(1-\alpha)))}.$$
--
--   These identities connect the class waiting-time model to the utility formulas used in the equilibrium and surplus analysis.
--
--   **Formalization Note** The standing assumptions include the explicit positive rates and cost stated in the model definition. Stability and $\gamma\in[0,1]$ keep every denominator positive.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), p. 12 (PDF 13), Lemma 1, Eq. (2); Online Appendix p. 1 (PDF 35), A.1

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

namespace PrivacyQueue.Control

/-- Lemma 1, p. 12: the two utilities after simplifying the three-class waits. -/
theorem lemma_1 (P : Params) (hS : P.Standing) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    Ud P γ = P.R - P.c *
      (P.α / (P.mu - P.α * P.lam * γ) +
       P.σ * (1 - P.α) * (P.mu + P.lam * P.α * (P.σ - 1)) /
         ((P.σ * P.mu - P.lam * (1 + P.α * (P.σ - 1))) *
          (P.σ * P.mu - P.lam * (P.α * P.σ + (1 - γ) * (1 - P.α))))) ∧
    Uw P γ = P.R - P.c *
      ((P.σ * (1 + P.α * (P.σ - 1)) * P.mu -
          P.lam * P.α * (P.α - 1) * (P.σ - 1) * (P.σ + γ - 1)) /
        (P.σ * (P.mu - P.lam * P.α * γ) *
          (P.σ * P.mu - P.lam * (P.α * P.σ + (1 - γ) * (1 - P.α))))) := by sorry

end PrivacyQueue.Control
