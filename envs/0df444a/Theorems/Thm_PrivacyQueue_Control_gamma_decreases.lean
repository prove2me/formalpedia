-- Prove2me | Theorems.Thm_PrivacyQueue_Control_gamma_decreases
-- name    : PrivacyQueue.Control.gamma_decreases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:05.312015+00:00
-- url     : https://prove2.me/theorems/150bd606-9228-4acf-923b-a65434f801d4
-- title:
--   Proof of Lemma 4 — Γ decreases with disclosure probability
-- statement:
--   In the noncritical parameter regime, the auxiliary function $\Gamma$ from the proof of Lemma 4 has derivative
--
--   $$\Gamma'(\gamma)=\lambda(1-\alpha(1+\sigma))\left(1-\frac{\sigma^2(\mu-\alpha\lambda)^2}{\bigl(\gamma\lambda(1-\alpha(1+\sigma))+(\sigma\mu-(1-\alpha)\lambda)\bigr)^2}\right).$$
--
--   This derivative is negative for $0\le\gamma<1$, and $\Gamma$ is strictly decreasing across $[0,1]$. This supplies the directional ingredient for the surplus comparison.
--
--   **Formalization Note** The printed strict derivative claim has the endpoint exception $\Gamma'(1)=0$. The derivative formula holds on $[0,1]$, while strict negativity is stated only on $[0,1)$. The auxiliary item excludes $\alpha(1+\sigma)=1$.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), Online Supplement p. 2 (PDF 49), proof of Lemma 4, derivative of Γ

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

namespace PrivacyQueue.Control

/-- Proof of Lemma 4, Online Supplement p. 2: Γ has negative derivative before γ = 1. -/
theorem gamma_decreases (P : Params) (hS : P.Standing)
    (hCritical : P.α * (1 + P.σ) ≠ 1) :
    (∀ γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt (Gam P)
        (P.lam * (1 - P.α * (1 + P.σ)) *
          (1 - P.σ ^ 2 * (P.mu - P.α * P.lam) ^ 2 /
            (γ * P.lam * (1 - P.α * (1 + P.σ)) +
              (P.σ * P.mu - (1 - P.α) * P.lam)) ^ 2)) γ) ∧
    (∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 →
      P.lam * (1 - P.α * (1 + P.σ)) *
        (1 - P.σ ^ 2 * (P.mu - P.α * P.lam) ^ 2 /
          (γ * P.lam * (1 - P.α * (1 + P.σ)) +
            (P.σ * P.mu - (1 - P.α) * P.lam)) ^ 2) < 0) ∧
    StrictAntiOn (Gam P) (Set.Icc (0 : ℝ) 1) := by sorry

end PrivacyQueue.Control
